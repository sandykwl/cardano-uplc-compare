# cardano-uplc-compare

This repository runs [cardano-uplc](https://github.com/sandykwl/cardano-uplc)
and plutus-core on the same inputs and reports every place where they differ.

cardano-uplc is a Haskell implementation of Untyped Plutus Core that does not
depend on plutus-core. plutus-core is the implementation the Cardano network
runs, so cardano-uplc has to behave exactly like it: write the same bytes,
accept and refuse the same inputs, and evaluate every term to the same result.
This repository lets anyone check that for themselves. It is kept separate
because it depends on plutus-core, the dependency cardano-uplc exists to avoid.

[`docs/guide.md`](docs/guide.md) explains each comparison in more detail: what
it does, why it is built that way, and how to read its output.

## What it checks

**Flat programs.** Both decoders read the same bytes. They must both accept or
both refuse. When both accept, they must have read the same program, and both
must write it back as the same bytes. The programs are compared as values, not
only as bytes, because a mistake made the same way in the writer and the
reader, such as two builtins with swapped tags, would leave the bytes equal.

**`Data` as CBOR.** Both encoders write the same `Data` values and must produce
the same bytes. Both decoders read the same bytes and must agree on whether to
accept them and, if they do, on the value.

**The ledger's `value` type.** Values made on each side are written by both and
read back by the other.

**Evaluation.** Both CEK machines run the same term. They must return the same
term, or fail with the same error and the same offending term. A generated
term can loop for ever, so plutus-core runs it first, with a budget, and a
term it cannot finish is skipped; the guide explains how that path is tested.

**Builtins.** The 33 builtins cardano-uplc's machine runs (the integer,
bytestring and bitwise ones, and `ifThenElse`) are applied to arguments at the
edges of their ranges. Each application is evaluated by both machines under
each of plutus-core's five builtin semantics variants, A to E, and the results
must match. Some applications are deliberately wrong: an argument of the wrong
type, a missing or extra force, too few or too many arguments.

**Each builtin's forces and arity.** For all 94 builtins cardano-uplc knows, a
grid of terms forces and applies the builtin different numbers of times. Both
machines must agree on where it stops being a value and becomes an error.

When only plutus-core accepts a flat program, the reason must be one
cardano-uplc does not cover yet: a builtin after tag 93. These are counted as
known gaps. Every other difference is a disagreement, printed with its input.

## Running it

You need GHC 9.6.7 and cabal. cardano-uplc is read from a checkout next to this
one, so the run always tests the commit that checkout holds. Its `cek-machine`
branch has the machine and the builtins:

```bash
git clone -b cek-machine https://github.com/sandykwl/cardano-uplc.git
git clone https://github.com/sandykwl/cardano-uplc-compare.git
cd cardano-uplc-compare
cabal update                    # the package index is pinned to 2026-09-24
cabal run -w ghc-9.6.7 cardano-uplc-compare -- 1000
```

The first build compiles plutus-core and about 150 other packages, which takes
a while. plutus-core's crypto is turned off in `cabal.project`, so no system
library is needed.

The number is how many cases each random family draws: 1000 programs, 1000
terms, 1000 applications of each builtin, and so on. The hand-built families
always run in full. With no number, it draws 10000.

Other ways to run it:

```bash
cabal run -w ghc-9.6.7 cardano-uplc-compare -- builtins 1000   # the builtins only
cabal run -w ghc-9.6.7 cardano-uplc-compare -- shapes          # forces and arity only
cabal run -w ghc-9.6.7 cardano-uplc-compare -- corpus DIR      # every .flat file under DIR
```

For a corpus, plutus's conformance tests are a good choice:

```bash
git clone --filter=blob:none --no-checkout https://github.com/IntersectMBO/plutus.git
cd plutus && git sparse-checkout set plutus-conformance/test-cases/uplc && git checkout master && cd ..
cabal run -w ghc-9.6.7 cardano-uplc-compare -- corpus plutus/plutus-conformance/test-cases/uplc
```

A `.flat` file may hold raw bytes, as plutus's do, or the bytes written out in
hex, as amaru's do.

Each family prints one summary line and its disagreements: up to ten for most
families, all of them for the builtins and for forces and arity. The
last line is `RESULT: no disagreements` or `RESULT: disagreements found`, and
in the second case the exit status is 1.

## Checking that it can fail

A clean run only means something if the comparison can fail. The script
`scripts/planted-bugs.py` plants known bugs in a copy of the cardano-uplc
checkout, one at a time, and runs the comparison against each:

```bash
python3 scripts/planted-bugs.py              # every bug
python3 scripts/planted-bugs.py readbit      # one of them
```

There are fourteen, at least one for each comparison: swapped builtin tags,
wrong `Data` chunking, a number reader that reads too far, a token quantity
out of range, reversed `case` branches, two machine mistakes, six builtin
mistakes, and a wrong arity. For each it prints `caught` and the families that reported it, or
`MISSED`. It exits with status 1 if any bug is missed. Your checkout is never
changed.

## What it does not check

The builtins cardano-uplc's machine does not run yet, and `constr` and `case`
at run time. Nor the cost of evaluation: costing is outside cardano-uplc's
scope, so its machine has no budget.

The reference is plutus-core 1.70.0.0, pinned with the package index in
`cabal.project`. Moving that pin is how the comparison moves to a newer
plutus-core.
