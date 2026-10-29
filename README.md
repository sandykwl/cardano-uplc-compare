# cardano-uplc-compare

Runs [cardano-uplc](https://github.com/sandykwl/cardano-uplc) and plutus-core
on the same inputs and reports any difference.

cardano-uplc reads and writes Untyped Plutus Core without depending on
plutus-core. A script's hash is taken over its bytes, so "it round-trips" is
not enough: it has to write exactly the bytes plutus-core writes, and accept
exactly the inputs plutus-core accepts. This tool checks that. It is a separate
repository because it depends on plutus-core, the dependency cardano-uplc exists
to avoid.

## What it compares

**Flat programs.** For every input, both decoders read the same bytes and must
agree on whether to accept them. When both accept, they must have read the same
program, compared value by value with builtins matched by name, and each must
re-encode it to the same bytes, so the encoders are compared too. Comparing
bytes alone would miss a mistake made the same way in both directions, such as
two builtins with swapped tags.

**`Data` as CBOR.** Both encoders write the same values and must produce the
same bytes. Both decoders read the same bytes and must agree on accepting and,
when they accept, on the value.

**The ledger's `value` type.** Values from each side are written by both and
read back by the other, and compared as values as well as bytes.

**Evaluation.** Both CEK machines run the same term and must return the same
term, or fail the same way with the same offending value. The terms use what
cardano-uplc's machine runs so far: variables, lambdas, application, delay,
force, constants and `error`, plus a few returned closures with `constr` and
`case` in their bodies, never run. A term can loop for ever and cardano-uplc's
machine has no budget, so plutus-core runs first, with one, and a term it does
not finish is skipped. One looping term is always included, and the run fails
if it is not skipped.

**Builtins.** The 33 builtins cardano-uplc's machine runs, the integer,
bytestring and bitwise ones and `ifThenElse`, are applied to arguments at the
edges of their ranges, and each application is evaluated by both machines
under each of plutus-core's five builtin semantics variants, A to E. The two
must agree on the result, or on the error and the term that caused it. Most
applications are saturated and well typed; the rest have an argument of the
wrong type, a missing or extra force, too few or too many arguments, or an
argument bound by a lambda. An application plutus-core cannot finish within a
very large budget is one the chain rejects, so cardano-uplc must not return a
value for it either.

**Each builtin's forces and arity.** For every builtin cardano-uplc knows, not
only the ones its machine runs, a grid of terms forces it up to three times,
applies it to up to seven arguments and sometimes forces it once more. A wrong
force count or arity moves the point where a builtin stops being a value and
becomes an error, so the two machines would disagree somewhere on the grid.
Where cardano-uplc does not run the builtin, it may stop with `NotSupported`
once plutus-core would have run it. `cardano-uplc-compare shapes` runs this
alone.

For flat, when only plutus-core accepts an input, the refusal must be what
cardano-uplc does not handle yet: builtins after tag 93. These are counted as
known gaps, by builtin tag, and only when plutus-core's program really calls
the builtin. Anything else is reported as a disagreement, with the input in
hex. For `Data`, every one-sided acceptance is a disagreement.

## The inputs

- **Generated programs and constants**, from the same generators as
  cardano-uplc's own tests (`src/Gen.hs` is a copy).
- **Damaged encodings**: a generated program's or value constant's bytes with a
  bit flipped, a byte replaced, inserted, deleted or appended, or the end cut
  off.
- **Random bytes** after a valid version.
- **Hand-built edge cases**, one family per reading rule: padded numbers,
  padding and the end of input, byte-string chunking, UTF-8, every term tag,
  every list of up to four type tags, every builtin tag, `data` constants,
  including bytes after the value, which plutus-core reads and ignores, and
  `value` constants that break each rule of the type.
- **Values** from cardano-uplc's generator, and values built by plutus-core's
  own constructors.
- **`Data` values and bytes**: generated values, each form of the writer at
  both sides of its boundary, inputs the reader must accept or refuse,
  including forms plutus-core never writes, and damaged encodings.
- **Terms to evaluate**, generated with variables that mostly point at an
  enclosing lambda and sometimes at index 0 or past them all, and with lambdas
  often applied straight away, so bodies run with something bound.
- **Builtin applications**, with integers at 0, ±1, the 64-bit limits, 2^8191,
  2^65536 and 2^262143, byte strings of length 0, 1, 64, 4096, 4097 and 65536,
  and indices, widths and shifts on either side of the byte string's length.
  `cardano-uplc-compare builtins N` runs this family alone.
- **A corpus of real programs**, any directory of `.flat` files.

## Running it

It needs GHC 9.6.7 and cabal. cardano-uplc is read from a checkout next to
this one, so a comparison is always of the commit that checkout holds. It
needs a cardano-uplc whose machine runs the builtins, which is on its
`cek-machine` branch:

```bash
git clone -b cek-machine https://github.com/sandykwl/cardano-uplc.git
git clone <this repository> cardano-uplc-compare
cd cardano-uplc-compare
cabal update                          # the index is pinned to 2026-09-24
cabal run -w ghc-9.6.7 cardano-uplc-compare -- 10000
```

The first build compiles plutus-core and about 150 packages. Its crypto is
turned off in `cabal.project`, so no system library is needed. The number is
how many cases each random family draws; the hand-built families are always
run whole.

To run a corpus, give it a directory. The conformance tests in the plutus
repository are the obvious one:

```bash
git clone --filter=blob:none --no-checkout https://github.com/IntersectMBO/plutus.git
cd plutus && git sparse-checkout set plutus-conformance/test-cases/uplc && git checkout master && cd ..
cabal run -w ghc-9.6.7 cardano-uplc-compare -- corpus plutus/plutus-conformance/test-cases/uplc
```

A `.flat` file may hold the bytes themselves, as plutus's do, or the bytes
written out in hex, as amaru's do. The run says how many files it read and how
many were hex, and fails if it found none.

The run exits with status 1 if there is any disagreement, and prints at most
ten of each family's.

## Checking that it can fail

A clean run means little unless the tool can fail. Put a known mistake into
the cardano-uplc checkout and run again. Each of these is reported at 300
cases:

- two builtins swapped in `DefaultFun`'s declaration, so their tags swap the
  same way in both directions: caught by comparing the decoded programs;
- a `Data` byte-string writer that cuts chunks at 63 bytes instead of 64:
  caught in the `Data` families and the flat ones that hold `data` constants;
- a word reader that takes an eleventh group: caught in the padded naturals;
- a quantity bound that lets 2^127 through: caught in the hand-built `value`
  constants;
- a machine that computes an argument before its function, or discharges a
  returned lambda's body from depth 0 instead of 1: caught in the evaluation
  family.

## What it does not compare

The other builtins, and `constr` and `case` at run time, which cardano-uplc's
machine does not run yet. Nor the cost of evaluation: costing is outside
cardano-uplc's scope.

The reference is plutus-core 1.70.0.0, pinned with the package index in
`cabal.project`. Moving the pin is how the comparison moves to a newer
plutus-core.
