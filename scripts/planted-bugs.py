#!/usr/bin/env python3
"""Plant known bugs in a copy of cardano-uplc and check the comparison catches each.

Usage: scripts/planted-bugs.py [NAME...]

It reads the cardano-uplc checkout beside this repository, as a normal run
does, or the one the UPLC environment variable names. The package's files are
copied once to a temporary directory, so the checkout is never changed. Each
bug is one edit to that copy; the comparison is built against it and run, and
the edit is undone before the next bug. A bug counts as
caught when the run fails and names at least one disagreement. With no names,
every bug is planted. The script exits with status 1 if any bug is missed.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
UPLC = os.environ.get("UPLC", os.path.join(os.path.dirname(HERE), "cardano-uplc"))
GHC = os.environ.get("GHC", "ghc-9.6.7")


def swap_builtins(src):
    # AddInteger and SubtractInteger change places in DefaultFun, so both
    # their flat tags swap, in the encoder and the decoder alike.
    return src.replace("    AddInteger\n", "    @@\n", 1).replace(
        "    SubtractInteger\n", "    AddInteger\n", 1).replace("    @@\n", "    SubtractInteger\n", 1)


def replace(*pairs):
    # Each old text must be there, or the edit gives None.
    def edit(src):
        for old, new in zip(pairs[::2], pairs[1::2]):
            if old not in src:
                return None
            src = src.replace(old, new, 1)
        return src
    return edit


# name: (what it is, file, edit, arguments to the comparison)
BUGS = {
    "swapped-builtins": (
        "AddInteger and SubtractInteger swapped in DefaultFun",
        "src/Cardano/UPLC/Builtin.hs", swap_builtins, ["300"]),
    "data-chunks": (
        "Data byte strings cut into chunks of 63 bytes, not 64",
        "src/Cardano/UPLC/Data/Cbor/Internal.hs",
        replace("BS.length bs > 64 = let (c, rest) = BS.splitAt 64 bs",
                "BS.length bs > 63 = let (c, rest) = BS.splitAt 63 bs"), ["300"]),
    "eleventh-group": (
        "the word reader takes an eleventh group",
        "src/Cardano/UPLC/Flat/Bits.hs",
        replace("        if shift == 63\n", "        if shift == 70\n"), ["300"]),
    "quantity-bound": (
        "a token quantity of 2^127 accepted",
        "src/Cardano/UPLC/Value.hs",
        replace("i < 2 ^ (127 :: Int) = Just", "i <= 2 ^ (127 :: Int) = Just"), ["300"]),
    "case-branches": (
        "case branches reversed when written and when read",
        "src/Cardano/UPLC/Flat.hs",
        replace("pushListWith putTerm (Vector.toList branches)",
                "pushListWith putTerm (Vector.toList (Vector.reverse branches))",
                "(Case () <$> go <*> (Vector.fromList <$> getListWith go))",
                "(Case () <$> go <*> (Vector.reverse . Vector.fromList <$> getListWith go))"),
        ["300"]),
    "argument-first": (
        "the machine computes an argument once before its function",
        "src/Cardano/UPLC/Machine.hs",
        replace("  Apply _ f x -> compute var (FrameAwaitFunTerm env x : stack) env f\n",
                "  Apply _ f x -> compute var [] env x >> compute var (FrameAwaitFunTerm env x : stack) env f\n"),
        ["300"]),
    "discharge-depth": (
        "a returned lambda's body discharged from depth 0, not 1",
        "src/Cardano/UPLC/Machine/CekValue.hs",
        replace("(DeBruijn 0) (substitute env 1 body)", "(DeBruijn 0) (substitute env 0 body)"), ["300"]),
    "slice": (
        "sliceByteString with a negative start keeps too few bytes",
        "src/Cardano/UPLC/Machine/Builtins/ByteString.hs",
        replace("Right (BS.take (fromIntegral len) (BS.drop (fromIntegral start) s))",
                "Right (BS.take (fromIntegral (max 0 (min (toInteger start + toInteger len) (toInteger (BS.length s)) - max 0 (toInteger start)))) (BS.drop (fromIntegral start) s))"),
        ["builtins", "500"]),
    "cons-range": (
        "variant E stops refusing a consByteString byte outside 0 to 255",
        "src/Cardano/UPLC/Machine/Builtins.hs",
        replace("  VariantD -> False\n  VariantE -> True", "  VariantD -> False\n  VariantE -> False"),
        ["builtins", "500"]),
    "readbit": (
        "readBit counts bytes from the wrong end",
        "src/Cardano/UPLC/Machine/Builtins/Bitwise.hs",
        replace("BS.index bs (n - 1 - i `div` 8)", "BS.index bs (i `div` 8)"), ["builtins", "500"]),
    "expmod": (
        "expModInteger checks its bounds before answering modulus 1",
        "src/Cardano/UPLC/Machine/Builtins/Integer.hs",
        replace("  | m == 1 = Right 0\n  | b == 0 && e < 0 = Left Failed\n  | outside b || outside e = Left Failed\n",
                "  | b == 0 && e < 0 = Left Failed\n  | outside b || outside e = Left Failed\n  | m == 1 = Right 0\n"),
        # Only a modulus of 1 shows it, beside an argument out of range or a zero
        # base with a negative exponent.
        ["builtins", "2000"]),
    "discharge-forces": (
        "a partial builtin discharged without its forces",
        "src/Cardano/UPLC/Machine/CekValue.hs",
        replace("(Builtin () f) !! forces)", "(Builtin () f) !! (forces * 0))"), ["builtins", "500"]),
    "arity": (
        "sha2_256 given two arguments where it takes one",
        "src/Cardano/UPLC/Machine/Builtins.hs",
        replace("  Sha2_256                        -> (0, 1)\n", "  Sha2_256                        -> (0, 2)\n"),
        ["shapes"]),
    "rotate": (
        "rotateByteString takes rem where it needs mod",
        "src/Cardano/UPLC/Machine/Builtins/Bitwise.hs",
        replace("r = k `mod` bits", "r = k `rem` bits"), ["builtins", "500"]),
}

DISAGREEMENTS = re.compile(r"^(.*?): .*?\b([1-9][0-9]*) disagreements$")


def copy_package(src, dst):
    # The package's own files are all a build needs: the top-level files and
    # the src and test directories.
    os.makedirs(dst)
    for name in os.listdir(src):
        path = os.path.join(src, name)
        if os.path.isfile(path):
            shutil.copy2(path, dst)
    for name in ("src", "test"):
        shutil.copytree(os.path.join(src, name), os.path.join(dst, name))


def project_file(tmp, copy):
    with open(os.path.join(HERE, "cabal.project"), encoding="utf-8") as f:
        text = f.read()
    text, n = re.subn(r"^packages:.*$", f"packages: {HERE} {copy}", text, count=1, flags=re.M)
    assert n == 1, "cabal.project has no packages line"
    path = os.path.join(tmp, "cabal.project")
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    return path


def main():
    names = sys.argv[1:] or list(BUGS)
    unknown = [n for n in names if n not in BUGS]
    if unknown:
        sys.exit(f"unknown bug {', '.join(unknown)}; known: {', '.join(BUGS)}")
    if not os.path.isdir(os.path.join(UPLC, "src", "Cardano", "UPLC")):
        sys.exit(f"no cardano-uplc checkout at {UPLC}")

    tmp = tempfile.mkdtemp(prefix="planted-")
    copy = os.path.join(tmp, "cardano-uplc")
    copy_package(UPLC, copy)
    project = project_file(tmp, copy)
    missed = []
    try:
        for name in names:
            what, rel, edit, args = BUGS[name]
            path = os.path.join(copy, rel)
            with open(path, encoding="utf-8", newline="") as f:
                original = f.read()
            planted = edit(original)
            if not planted or planted == original:
                sys.exit(f"{name}: the code it edits is not in {rel}; this script needs updating")
            with open(path, "w", encoding="utf-8", newline="") as f:
                f.write(planted)
            try:
                run = subprocess.run(
                    ["cabal", "run", "-v0", "-w", GHC, f"--project-file={project}",
                     f"--builddir={os.path.join(HERE, 'dist-newstyle', 'planted')}",
                     "cardano-uplc-compare", "--", *args],
                    cwd=HERE, capture_output=True, text=True)
            finally:
                with open(path, "w", encoding="utf-8", newline="") as f:
                    f.write(original)
            caught = [m.group(1) + f" ({m.group(2)})" for line in run.stdout.splitlines()
                      if (m := DISAGREEMENTS.match(line))]
            if run.returncode == 1 and caught:
                print(f"caught  {name}: {what}\n        in {'; '.join(caught)}")
            else:
                missed.append(name)
                tail = (run.stderr or run.stdout).strip().splitlines()[-3:]
                print(f"MISSED  {name}: {what} (exit {run.returncode})")
                for line in tail:
                    print(f"        {line}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    print(f"{len(names) - len(missed)} of {len(names)} planted bugs caught")
    sys.exit(1 if missed else 0)


if __name__ == "__main__":
    main()
