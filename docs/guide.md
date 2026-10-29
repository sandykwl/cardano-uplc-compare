# How the comparisons work

This guide is for a developer who wants to know what `cardano-uplc-compare`
actually checks before trusting its result. It assumes you can read a little
Haskell, and nothing about Plutus beyond what is explained here. The README
says how to run the tool; this page says what each part does and why.

## The idea

Cardano stores smart contracts as programs in Untyped Plutus Core (UPLC). Every
node must agree on three things about a program:

- its bytes, because a script is identified by a hash of its serialised form,
  the *flat* encoding;
- whether those bytes are a valid program at all;
- what the program evaluates to, because that decides whether a transaction is
  valid.

plutus-core is the implementation the network runs. cardano-uplc is a separate
implementation of the same language. If the two differ anywhere, a script that
one accepts the other might reject, and a program cardano-uplc builds might not
have the hash its author expects. So the test is whether cardano-uplc does
exactly what plutus-core does.

The tool answers that by running both on the same inputs and comparing. The
source is in `src/`:

| Module | What it compares |
| --- | --- |
| `Main.hs` | Flat programs; it also runs every other family and prints the result |
| `Cbor.hs` | `Data` values written and read as CBOR |
| `Value.hs` | The ledger's `value` type |
| `Eval.hs` | The two CEK machines on generated terms |
| `Family.hs` | The builtins, under each semantics variant |
| `Shape.hs` | Each builtin's number of forces and arguments |
| `Convert.hs` | Turns plutus-core's programs, `Data` and values into cardano-uplc's types |
| `Gen.hs` | Generators, copied from cardano-uplc's own tests |
| `Bits.hs` | A small bit writer for hand-built inputs |

## Four possible verdicts

For a decoder, each input ends in one of four ways:

| Verdict | Meaning |
| --- | --- |
| both accept | both read a program, the same one, and write it back as the same bytes |
| both refuse | neither reads a program; the reasons may differ, since error messages are not part of the contract |
| known gap | only plutus-core reads it, because it calls a builtin cardano-uplc does not have yet |
| disagreement | anything else; printed with the input in hex |

A known gap is counted only when plutus-core's decoded program really calls a
builtin after tag 93. If cardano-uplc refused for that reason but plutus-core's
program does not contain such a builtin, cardano-uplc has misread the bytes,
and that is a disagreement.

## Flat programs

### Why compare values and not only bytes

The obvious check is: decode with both, re-encode with both, compare bytes.
That misses a whole class of mistakes. Suppose cardano-uplc had `addInteger`
and `subtractInteger` swapped in its tag table. Its decoder reads tag 0 as
`subtractInteger`, and its encoder writes `subtractInteger` as tag 0. The
bytes round-trip perfectly, and every script that adds would subtract.

So when both decoders accept, `Convert.hs` turns plutus-core's program into
cardano-uplc's types, matching builtins by *name*, never by tag, and the two
programs must be equal. The swapped-tag bug is one of the planted bugs, and
this is the check that catches it.

### The inputs

- **Generated programs**, from cardano-uplc's own test generators (`Gen.hs`
  is a copy). They are well formed, so they test the encoder: plutus-core must
  read cardano-uplc's bytes and write the same bytes back.
- **Damaged encodings.** A generated program's bytes with one change: a bit
  flipped, a byte replaced, inserted or deleted, the end cut off, a byte added at the end.
  These test the decoders on input that is nearly valid, which is where
  mistakes hide.
- **Random bytes** after a valid version header.
- **Hand-built edge cases**, one family per reading rule of the format. They
  are built with `Bits.hs`, a writer separate from cardano-uplc's, because they
  must include bytes cardano-uplc would never write: numbers padded with extra
  groups, every amount of padding at the end, byte strings split into chunks
  in different ways, invalid UTF-8, every term tag, every list of up to four
  type tags (69,905 lists, each followed by five kinds of value: 349,525
  inputs), every builtin tag from 0 to 127, `data`
  constants with bytes after the value, and `value` constants that break each
  rule of the type.

## `Data` as CBOR

`Data` is the type smart contracts use for their arguments, and it is
serialised as CBOR. `Cbor.hs` checks both directions:

- **writing**: both encoders write the same values, and the bytes must be
  equal. The values come from a generator that aims at the boundaries of the
  encoding, such as a byte string of 64 bytes against 65, where the writer
  switches to chunks;
- **reading**: both decoders read the same bytes, including forms plutus-core
  never writes but must still accept or refuse, and damaged encodings. They
  must agree on accepting and on the value.

Here every one-sided acceptance is a disagreement; there are no known gaps.

## The `value` type

The ledger's multi-asset value is a map of currencies to maps of tokens to
quantities, with rules: no zero quantities, no empty token maps, keys at most
32 bytes, quantities within 128 bits. `Value.hs` converts values both ways.
Values from cardano-uplc's generator must be written by plutus-core as the same
bytes and read back as the same value. Values built through plutus-core's own
constructors must be read by cardano-uplc as the same value. Hand-built
programs break each rule once.

## Evaluation

A UPLC program is evaluated by a CEK machine. `Eval.hs` runs both machines on
the same term and compares what they return.

### What "the same" means

A successful evaluation returns a term, and the two terms must be equal. A
failed one returns an error. plutus-core reports an error together with the
term that caused it, and cardano-uplc does the same, so the comparison is on
both: the same kind of error and the same offending term. Comparing the kind
alone would let a machine that fails in the wrong place pass.

plutus-core's errors are translated into cardano-uplc's names, for example:

| plutus-core | cardano-uplc |
| --- | --- |
| `CekEvaluationFailure` caused by `error` | `ErrorTerm` |
| `CekEvaluationFailure` caused by a builtin | `BuiltinFailure` |
| `OpenTermEvaluatedMachineError` | `FreeVariable` |
| `NonFunctionalApplicationMachineError` | `NotAFunction` |
| `NonPolymorphicInstantiationMachineError` | `NotDelayed` |
| `UnliftingMachineError` | `BuiltinArgumentType` |
| `BuiltinTermArgumentExpectedMachineError` | `BuiltinNeedsArgument` |
| `UnexpectedBuiltinTermArgumentMachineError` | `BuiltinNeedsForce` |

### The terms

The generator builds terms from variables, lambdas, application, `delay`,
`force`, small constants and `error`. Variables mostly point at an enclosing
lambda, and now and then at index 0 or past all of them, to reach the
free-variable error. Lambdas are often applied straight away, so their bodies
run with something bound; without that, a mistake in how variables are looked
up would rarely show. A few hand-built terms return closures with `constr` and
`case` in their bodies, never run, so turning a closure back into a term is
checked for those too.

### Terms that never finish

An untyped term can loop for ever, and cardano-uplc's machine has no budget.
So plutus-core runs each term first, with a budget, and a term it cannot
finish is skipped. One term that loops is always included, and the family
fails unless it was skipped: otherwise the skipping path would never be
tested. When plutus-core does finish, cardano-uplc must finish too; a time
limit turns a hang into a reported disagreement.

## Builtins

Builtins are the primitive operations: `addInteger`, `sliceByteString`,
`readBit` and the rest. `Family.hs` compares the 33 that cardano-uplc's
machine runs: the integer, bytestring and bitwise builtins, and `ifThenElse`.

### Semantics variants

plutus-core's builtins do not behave identically in every era. It has five
*semantics variants*, A to E, and the ledger picks one from the script's
Plutus version and the protocol version. Some differences between them:

- C and E refuse a `consByteString` byte outside 0 to 255; A, B and D wrap it;
- D and E put bounds on most integer and bytestring arguments, such as
  integers below 2^262143, and on the amount of a shift or rotation;
- A and B behave the same; they differ only in cost, which is not compared.

Every application is evaluated under all five, so each variant's rules are
checked, not just the newest.

### The arguments

Each builtin has a signature: how many forces it takes and the kind of each
argument. The kinds say where the edge values come from. An integer argument
is drawn from small values, the 64-bit limits, and the limits plutus-core
checks: 2^8191 for `expModInteger`, the 8192-byte width limit of
`integerToByteString`, 2^262143 for variants D and E. An index or a shift is
drawn around the length of the byte string beside it, in bytes and in bits, on
both sides of each end. Byte strings are of length 0, 1, 2, 64, 4096, 4097,
65536 and others.

### Wrong applications

About three in five applications are saturated and well typed. The rest are
wrong on purpose:

- one argument replaced by a value of the wrong type, or by a lambda or `error`;
- too many or too few forces;
- too few arguments, with or without a force after them;
- one argument too many;
- an argument passed through a lambda instead of written in place.

A wrong application must fail the same way in both machines, with the same
offending term.

### The budget, again

Builtins always finish, so here plutus-core gets a budget so large it cannot
run out on any reasonable input. If it does run out anyway, the term is one the
chain would reject, and cardano-uplc must not return a value for it.

## Forces and arity

A builtin takes a fixed number of forces, then a fixed number of arguments. If
cardano-uplc had either number wrong for some builtin, the machine would turn
that builtin into a value or an error at the wrong point. `Shape.hs` checks all
94 builtins cardano-uplc knows, including the ones its machine does not run
yet. For each it builds a grid: up to three forces, then up to seven unit
arguments, then sometimes one more force, 64 terms per builtin. Wherever
plutus-core returns a partial application, cardano-uplc must return the same
term. Elsewhere, a builtin cardano-uplc does not run yet may stop with
`NotSupported`.

## Reading the output

Here is part of a run at 200 cases, against cardano-uplc with its builtins:

```
decoder, mutated encodings: 200 inputs: both accept 48, both refuse 152, 0 known gaps, 0 disagreements
builtin tags: 128 inputs: both accept 94, both refuse 22, 12 known gaps, 0 disagreements
  gaps: builtin tag 94 1; builtin tag 95 1; …
machine, generated terms: 204 terms, 203 agree, 1 skipped for plutus-core's budget, 0 disagreements
  agreed on: ErrorTerm 19; FreeVariable 14; NotAFunction 20; NotDelayed 27; a constant 51; a delay 31; a lambda 41;
builtins, 200 applications of each of 33 builtins under each of 5 variants: 33000 evaluations, 0 disagreements
  per builtin, agree/skipped for plutus-core's budget/disagree, under A B C D E:
  AddInteger                200/0/0 | 200/0/0 | 200/0/0 | 200/0/0 | 200/0/0
  ReplicateByte             184/16/0 | 184/16/0 | 184/16/0 | 184/16/0 | 184/16/0
  …
  VariantE: BuiltinArgumentType 695; BuiltinFailure 897; BuiltinNeedsArgument 660; BuiltinNeedsForce 9; ErrorTerm 144; NotAFunction 205; a constant 3658; a delay 11; a lambda 32; another term 273;
RESULT: no disagreements
```

Each family prints one line: how many inputs, how each ended, and how many
disagreements. Below it come the details that make the line believable. The
`agreed on` list shows which outcomes the agreement covered; a family where
every term failed the same way would agree and test nothing, so it matters
that constants, lambdas, delays and each error all appear. In the builtin
table each cell is agreed/skipped/disagreed for one variant. `replicateByte`
has skips because plutus-core charges for an application before running it,
and a length such as 2^63 costs more than even its very large budget.
cardano-uplc then must not return a value, and it did not. Any disagreement
is printed after the summary with the term and both answers.

## A corpus

`cardano-uplc-compare corpus DIR` reads every `.flat` file under a directory
and runs the decoder comparison on each. plutus's conformance tests are the
natural corpus. A file may hold raw bytes or hex text; raw flat bytes start
with the major version, 1, which is not a hex digit, so the two are never
confused.

## Checking that it can fail

A comparison that never reports anything might be broken. `scripts/planted-bugs.py`
plants fourteen known bugs, one at a time, in a copy of the cardano-uplc
checkout, and runs the comparison against each. Every one must be caught.

| Bug | Families that reported it |
| --- | --- |
| `addInteger` and `subtractInteger` swapped in the tag table | generated programs, builtin tags |
| `Data` byte strings cut into chunks of 63 bytes | the `Data` families, and flat programs with `data` constants |
| the number reader takes an eleventh group | padded numbers |
| a token quantity of 2^127 accepted | hand-built `value` constants |
| `case` branches reversed in writing and reading | generated programs, damaged encodings |
| the machine computes an argument before its function | evaluation, builtins |
| a returned lambda's body discharged from the wrong depth | evaluation, builtins |
| `sliceByteString` with a negative start | builtins |
| variant E stops refusing a `consByteString` byte above 255 | builtins, under E |
| `readBit` counts bytes from the wrong end | builtins |
| `expModInteger` checks bounds before answering modulus 1 | builtins |
| a partial builtin turned back into a term without its forces | builtins |
| `rotateByteString` takes `rem` where it needs `mod` | builtins |
| `sha2_256` given two arguments where it takes one | forces and arity |

The inputs are random, so how many disagreements each bug causes changes from
run to run: the swapped builtins show up a handful of times, the
`rotateByteString` mistake hundreds. The `expModInteger` one shows only for a
modulus of 1 beside an argument out of range, or beside a zero base with a
negative exponent, so the modulus is drawn from 1, 0, -1 and 2 two times in
five, and this bug is planted with 2,000 applications of each builtin.

## What is not compared

- builtins cardano-uplc's machine does not run yet, and `constr` and `case`
  at run time;
- the cost of evaluation, since costing is outside cardano-uplc's scope;
- speed.

## Moving to a newer plutus-core

`cabal.project` pins plutus-core to 1.70.0.0 and the package index to a date,
so a run can be repeated exactly. To compare against a newer plutus-core, move
both pins, build, and run. Any new disagreement is either a change in
plutus-core that cardano-uplc has to follow, or a mistake in the comparison;
either way it needs reading before the pin is kept.
