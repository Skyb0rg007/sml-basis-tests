# Standard ML Basis Library test suite

Unit tests and property-based tests for the Standard ML Basis Library, written
to run unmodified on any Standard ML implementation.

Everything the Basis leaves to the implementation is an *input*: either read
from the implementation itself, or declared in a configuration structure the
suite is a functor over. No test hard-codes a word size, an integer precision,
a path separator, or a floating point tolerance.

## Quick start

```sh
run/smlnj.sh          # SML/NJ, via CM and ml-build
run/mlton.sh          # MLton, via the MLB file
run/polyml.sh         # Poly/ML, via the sequential loader
run/mlkit.sh          # MLKit, reads the same MLB file as MLton
```

Each script accepts the suite's own options:

```
--seed N       seed for the random generator (default 20260101)
--trials N     trials per property (default 100)
--max-size N   largest generated size (default 40)
--only PAT     run only tests whose full name contains PAT
--verbose      list passing tests as well as failing ones
--help
```

The process exits non-zero if anything failed, so it drops straight into CI.

## What makes it portable

**Nothing outside the required Basis.** No `SMLofNJ.*`, no `MLton.*`, no
compiler-specific library. Structures the Basis marks optional (`IntInf`,
`Int64`, `Real32`, `Posix`, `Unix`, `PackWord*`) are not referenced at all,
since naming an absent structure is a compile-time error rather than something
a run-time flag could skip.

**Three build descriptions, one source list.** `build/sources.txt` is the
dependency order; `build/sources.cm` (CM), `build/sources.mlb` (MLB) and
`build/load.sml` (a plain `use` sequence) are generated from it, so they cannot
drift apart.

**Facts are read, not assumed.** `Int.precision`, `Int.maxInt`, `Word.wordSize`,
`Char.maxOrd`, `Real.precision`, `Real.radix`, `String.maxSize` and
`Vector.maxLen` are discoverable from inside the language, so the tests read
them and derive their boundary values at run time. The Word tests compute the
top bit and the shift-past-the-end amount from `Word.wordSize`; they pass
unchanged on a 32-bit MLton and a 63-bit SML/NJ.

**What cannot be discovered is declared.** See below.

**A run is reproducible.** The generator threads its state explicitly rather
than keeping it in a `ref`, because the Definition leaves evaluation order
unspecified and a `ref`-based generator would hand different values to
different compilers. Each property is seeded from the run seed together with
its own fully qualified name, so adding a test does not perturb the data every
later property sees. Same seed, same inputs, on every implementation.

## Configuration

`src/config/config.sml` defines `TEST_CONFIG`. Porting means writing one
structure that matches it and pointing `src/config/selected.sml` at it.

| Field | What it declares |
| --- | --- |
| `implName` | Name shown in the run header |
| `hasIEEEReals` | `Real` is IEEE 754, with infinities and NaNs |
| `hasSignedZero` | `0.0` and `~0.0` are distinguishable via `signBit` |
| `hasSubnormals` | Subnormal values exist and `Real.class` reports them |
| `hasRoundingModes` | `IEEEReal.setRoundingMode` actually takes effect |
| `realFromStringAcceptsHex` | `Real.fromString` reads `0x1.8p3` (an extension) |
| `mathToleranceUlps` | Slack allowed for the `Math` functions, in ulps |
| `charPredicatesAreAscii` | `Char.isAlpha` and friends are false above 127 |
| `intOverflowRaises` | Integer overflow traps rather than wrapping |
| `pathStyle` | `UNIX` or `WINDOWS`, selecting the `OS.Path` expectations |
| `hasFileSystem` | Files can be created, read and removed |
| `scratchDir` | Where the file tests may write |
| `hasProcessEnv` | `OS.Process.getEnv` returns real answers |
| `hasSymbolicLinks` | The host has symbolic links, so `isLink`/`readLink` mean something |
| `canSpawnProcesses` | `OS.Process.system` can run a child process |
| `hasPollingIO` | `OS.IO.poll` works on descriptors from ordinary files |
| `canPollBothDirections` | One poll descriptor may carry `pollIn` and `pollOut` together |
| `timeResolutionNanos` | Granularity of `Time.time`, in nanoseconds |

Three configurations ship: `ConfigUnix` (the default), `ConfigWindows`, and
`ConfigMinimal`, which assumes nothing beyond what the Definition requires and
is the right starting point when bringing up a new implementation.

A test that does not apply is reported as `skip` with the reason, never
silently dropped — otherwise a suite could shrink to nothing on a system that
declares everything unsupported and still look green.

The dividing line is deliberate: a configuration declares *intended* behaviour,
so the suite compares the implementation against a specification rather than
against itself. Auto-detecting these facts would make every test vacuous.

## Property-based testing

Properties are `Prop.forAll (name, generator, printer, predicate)`, run for
`--trials` iterations with the size swept across `--max-size`. There is no
shrinking, as specified: a falsifying input is reported exactly as generated,
which is why `Show.real` formats with `StringCvt.EXACT` — the default
formatting keeps about twelve significant digits and would print two different
reals identically.

The generator is a 30-bit LCG whose multiply is done in 15-bit limbs, so every
intermediate stays below 2^30 and it runs correctly for any `Word.wordSize` of
30 or more. Integer generators bias towards `maxInt`, `minInt` and their
neighbours, since that is where conversions and overflow checks break.

### `Assert.hide`

`Vector.sub (#[1,2,3], ~1)` has entirely constant arguments, so an optimising
compiler may evaluate it at compile time. Then the test no longer exercises the
library, and a compiler whose constant folder disagrees with its own library
can fail to compile the suite outright — Poly/ML 5.7.1 reports `Overflow
unexpectedly raised while compiling` for exactly that expression. Bounds
checking tests therefore route their index through `Assert.hide`, which adds a
zero read from mutable storage. A branch on a `ref` is not enough: an optimiser
may distribute the surrounding call into both arms and fold the constant one.

## Coverage

Every structure the Basis Library marks as **required**:

`Array` · `ArraySlice` · `BinIO` · `BinPrimIO` · `Bool` · `Byte` · `Char` ·
`CharArray` · `CharArraySlice` · `CharVector` · `CharVectorSlice` ·
`CommandLine` · `Date` · `General` · `IEEEReal` · `Int` · `IO` · `LargeInt` ·
`LargeReal` · `LargeWord` · `List` · `ListPair` · `Math` · `Option` · `OS` ·
`OS.FileSys` · `OS.IO` · `OS.Path` · `OS.Process` · `Position` · `Real` ·
`String` · `StringCvt` · `Substring` · `Text` · `TextIO` · `TextIO.StreamIO` ·
`TextPrimIO` · `Time` · `Timer` · `Vector` · `VectorSlice` · `Word` · `Word8` ·
`Word8Array` · `Word8ArraySlice` · `Word8Vector` · `Word8VectorSlice`

1299 tests at run time, from 1115 in the source: 681 unit tests and 434
properties, some of which are generic over a signature and instantiated once
per required instance. At the default 100 trials a full run evaluates roughly
43,000 generated cases.

Eight of those structures are monomorphic sequences, three are `WORD`
instances, three are `INTEGER` and two are `REAL`. Testing each by hand would
be the same file copied fourteen times, so the tests for those are written
once against the signature (`gen-mono-seq.sml`, `gen-mono-slice.sml`,
`gen-numeric.sml`) and applied to every instance in `test-instances.sml`. The
hand-written `Word`, `Int` and `Real` suites remain and go deeper on the
default types; the generic ones give breadth across all the instances.

### Checking that nothing was missed

`tools/required-members.txt` lists every value, exception and constructor the
required part of the Basis specifies — 992 entries, cross-checked against the
expanded signatures MLton reports for `-show-basis` so the list is not just
what came to mind. `tools/check-coverage.sh` verifies that each one is
exercised somewhere in the test sources, resolving both the structure
abbreviations the tests use and the generic functors' parameters against every
instance they are applied to:

```
$ tools/check-coverage.sh
NOT CALLABLE IN-PROCESS  OS.Process.exit  (terminates the process, ...)
NOT CALLABLE IN-PROCESS  OS.Process.terminate  (terminates the process, ...)

checked 990 required members, 0 not mentioned in the test sources
2 further members cannot be called from inside a running test
```

The two exceptions are `OS.Process.exit` and `OS.Process.terminate`: calling
either ends the run, so they are listed with that reason rather than silently
skipped.

This is a coverage *floor*, not a proof. It shows that no required member was
overlooked; it does not claim that every test of every member is a thorough
one.

**Not covered**, and deliberately so: the optional structures (`IntInf`,
`Int64`, `Word32`, `Real32`, `Array2`, `Posix`, `Unix`, `Windows`, `Socket`,
`PackWord*`, `PackReal*`, the `Wide*` family). Naming an absent structure is a
compile-time error, so a suite that must run everywhere cannot reference them
at all. Adding them means adding a file and a line to the build description.

## Layout

```
src/framework/   random, generators, printers, assertions, test tree, runner
src/config/      TEST_CONFIG, the shipped configurations, and the selection
src/tests/       one functor over TEST_CONFIG per Basis structure (35 files),
                 including gen-*.sml, generic over a signature and applied to
                 every required instance
src/main.sml     command line entry point
build/           sources.txt and the three build descriptions generated from it
run/             one script per implementation
tools/           the required-member inventory and the coverage checker
```

## Results on three implementations

Run at the defaults. These are what the suite reports, with the reading of the
specification that each test encodes; where the Basis genuinely permits either
behaviour the test accepts both, or is gated by configuration.

| | passed | failed | errored | skipped |
| --- | --- | --- | --- | --- |
| SML/NJ 2026.1 (63-bit int and word) | 1273 | 21 | 0 | 5 |
| MLton 20241230 (32-bit int and word) | 1292 | 2 | 0 | 5 |
| Poly/ML 5.7.1 (63-bit int and word) | 1288 | 4 | 2 | 5 |

1299 tests in each column. "Errored" means an unexpected exception escaped, as
opposed to an assertion returning false; the two are counted separately so
that a library raising something surprising is never mistaken for a test
simply being false. The five skips are the three Windows `OS.Path` tests, the
hexadecimal real literal test, and the combined-direction poll test described
below.

**SML/NJ 2026.1** — 21 failures, from nine distinct defects:

- `String.isSubstring "" ""` is `false`. The empty string is a substring of
  every string; `isSubstring "" "a"` and `isPrefix "" ""` are both `true`.
- `StringCvt.skipWS` does not skip `\f` or `\v`, although `Char.isSpace`
  reports both as whitespace.
- `Vector.update`, `CharVector.update` and `Word8Vector.update` perform no
  bounds check: index `3` and index `~1` on a three-element vector both return
  normally instead of raising `Subscript`. The array versions are checked
  correctly, so this is specific to the immutable update.
- `TextIO.inputAll` and `BinIO.inputAll` raise `Io` on an empty stream. This
  reaches the functional `StreamIO` layer too, which is where most of the
  eighteen failures come from.
- `Date.fromString` does not skip leading whitespace, though every other
  scanner in the implementation does.
- `Date.toTime` followed by `Date.fromTimeUniv` is off by twelve hours for a
  date carrying an explicit UTC offset, so no date round-trips through a time.
- `LargeInt.fmt StringCvt.HEX` emits lower-case digits while `Int.fmt`,
  `Word.fmt`, `LargeWord.fmt` and `Position.fmt` all emit upper case.
- `OS.IO.poll` **terminates the runtime with a segmentation fault** when a
  single poll descriptor carries both `pollIn` and `pollOut`. Each direction
  alone is fine, and so are several separate descriptors in one call. Because
  a crash takes the rest of the run with it, the combined case is behind
  `canPollBothDirections`, which defaults to off; the individual directions
  are tested unconditionally.
- `Math.pow` has a relative error of about 1e-10 (roughly 184,000 ulps) for
  non-trivial exponents, while `exp` and `ln` are exact. The Basis mandates no
  accuracy for these, so this is a quality observation rather than a
  conformance failure — it is what the `pow` law reports at the default
  4096-ulp tolerance, and raising `mathToleranceUlps` silences it.

**MLton 20241230** — 2 failures:

- `Bool.fromString "   true"` is `NONE`; leading whitespace is not skipped,
  though `Int.fromString "   42"` correctly returns `SOME 42`.
- `TextIO.endOfStream` stays `false` after `inputAll` has consumed the whole
  stream. Draining the same stream with `input1` sets it correctly.

**Poly/ML 5.7.1** — 6 failures:

- `Real.fromString` rejects `"inf"`, `"infinity"` and `"nan"`, which are in the
  Basis grammar and which its own `Real.toString` produces, so the special
  values do not round-trip.
- `OS.Path.mkRelative` accepts a relative `relativeTo` argument instead of
  raising `Path`. `mkAbsolute` rejects it correctly.
- `Date.fmt ""` raises `Date`. An empty format string should produce an empty
  string, as it does on the other two.
- `LargeWord.fromInt ~1` yields `7FFFFFFFFFFFFFFF` rather than all ones, even
  though `LargeWord.wordSize` is 64 and `LargeWord.notb 0w0` and
  `LargeWord.- (0w0, 0w1)` both correctly give `FFFFFFFFFFFFFFFF`.
- `Word8.toLargeX` does not sign-extend into the top bit: `0wxFF` becomes
  `7FFFFFFFFFFFFFFF` instead of `FFFFFFFFFFFFFFFF`. `Word.toLargeX` is
  correct, so only the narrower source width is affected.
- `LargeWord.~>> (0w1, 0w64)` yields `1` rather than `0`; shifting a positive
  value right by the full word width must clear it. `LargeWord.>>` handles the
  same case correctly.
- Separately, 5.7.1 cannot compile `Vector.sub` or `Array.sub` applied to a
  constant sequence at a negative constant index. That is worked around by
  `Assert.hide` rather than by dropping the tests.

Poly/ML 5.7.1 dates from 2018 and is what Ubuntu ships; a current release may
behave differently.
