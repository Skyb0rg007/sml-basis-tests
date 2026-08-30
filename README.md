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
run/mlkit.sh          # MLKit, reads an MLB file as MLton does
```

The first three build a description that includes the optional structures
that implementation provides. Pass `--core` as the first argument to build the
portable description instead, the one that names no optional structure at all:

```sh
run/mlton.sh --core --only Word
```

`run/mlkit.sh` does not currently produce a binary: MLKit 4.7.22 stops with an
internal compiler error that has nothing to do with this suite. See the last
section.

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

**Nothing outside the required Basis, in the portable core.** No `SMLofNJ.*`,
no `MLton.*`, no compiler-specific library. Every file under `src/tests/`
names only structures the Basis requires, so it compiles anywhere.

**Optional structures are declared, not detected.** Naming an absent structure
is a compile-time error rather than something a run-time flag could skip, so
`IntInf`, `Int32`, `PackWord32Big` and the rest cannot appear in a file that
must compile everywhere. They live under `src/optional/` instead, and which of
them a build names is a *profile*: `build/optional/mlton.txt` lists the files,
`src/optional/opt-mlton.sml` applies them to the configuration. This is the
same division the configuration draws — what cannot be discovered from inside
the language is written down once, per implementation. `opt-none.sml` is the
profile that names none of them, and it is what the portable descriptions use.

**A missing required member is supplied, and declared.** An implementation may
be missing something the Basis requires. That is a finding, but on a
whole-program compiler it is a fatal one: the suite does not fail that test, it
fails to compile, and the thousand tests that have nothing to do with the
missing member never run either. A build may therefore supply the member from
`src/compat/`, selected by an `@compat` marker the same way a profile is. What
it must not do is then report a pass for it. Every substituted member is named
in `Compat.substituted`, the tests that exercise it are skipped with that as
the reason, and the run header prints the list — a suite that tests its own
code and calls the result conformance is worse than one that does not run.

`src/compat/compat-mlkit.sml` is the only one so far. MLKit 4.7.22 has 985 of
the 992 required members; it lacks `String.scan`, `Real.toDecimal`,
`Real.fromDecimal`, the `LargeReal` pair of those, and `Timer.checkCPUTimes`
and `Timer.checkGCTime`. Six are supplied by delegating to what MLKit does
have — `String.scan` is `Char.scan` applied until it declines, and `toDecimal`
goes through MLKit's own `Real.fmt` and `IEEEReal.fromString`. The seventh
cannot be: MLKit exposes no collector times at all, so `checkGCTime` returns
zero. That one is a stub, not an implementation, which is exactly why the skip
matters.

**Six build descriptions, one source list.** `build/sources.txt` is the
dependency order, with an `@optional` marker where the profile's files go.
`tools/gen-builds.sh` expands it, along with the `@compat` marker, into
`build/sources.cm` (CM),
`build/sources.mlb` (MLB) and `build/load.sml` (a plain `use` sequence) for the
portable profile, and into `build/sources-smlnj.cm`, `build/sources-mlton.mlb`
`build/load-polyml.sml` and `build/sources-mlkit.mlb` for the four
implementations with a profile of their own. They are generated, so they
cannot drift apart.

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
per required instance — 536 properties actually run. At the default 100 trials
that is about 54,000 generated cases. The optional structures below add 111
more tests in the source and, on MLton's profile, 583 at run time and another
29,000 generated cases.

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

checked 990 required members and 113 members of the
optional structures' own signatures, 0 not mentioned in the test sources
2 further members cannot be called from inside a running test
```

`tools/optional-members.txt` holds that second list. It covers only the
surface the optional structures *add* — the part of `INT_INF` that `INTEGER`
does not describe, and `PACK_WORD`, `PACK_REAL` and `ARRAY2`, which no
required structure implements. `Int32.quot` is not listed beside `Int.quot`,
because both are checked against the same line of the same generic file and
listing it twice would say nothing new. The checker reads the instance lists
out of `src/optional/opt-*.sml`, so adding a structure to a profile brings it
into the coverage check with it.

The two exceptions are `OS.Process.exit` and `OS.Process.terminate`: calling
either ends the run, so they are listed with that reason rather than silently
skipped.

This is a coverage *floor*, not a proof. It shows that no required member was
overlooked; it does not claim that every test of every member is a thorough
one.

### Optional structures

The Basis marks a second group of structures optional. They are not part of
the portable core for the reason given above — naming one that is absent is a
compile-time error — but the widely provided ones are covered by a profile
per implementation:

`IntInf` · `Int32` · `Int64` · `FixedInt` · `Word32` · `Word64` · `SysWord` ·
`Real32` · `Real64` · `PackWord16Big` · `PackWord16Little` · `PackWord32Big` ·
`PackWord32Little` · `PackWord64Big` · `PackWord64Little` · `PackRealBig` ·
`PackRealLittle` · `PackReal32Big` · `PackReal32Little` · `PackReal64Big` ·
`PackReal64Little` · `Array2` · `IntVector` · `IntArray` · `IntVectorSlice` ·
`IntArraySlice` · `RealVector` · `RealArray` · `RealVectorSlice` ·
`RealArraySlice`

No implementation provides all of them — Poly/ML has no `Int64` or `Real32`,
SML/NJ no `IntVector` — so each profile names what its own has, which is why
the three columns in the results table below hold different numbers of tests.

Most of these are further instances of signatures the suite already tests
generically, so they cost a line each: `Int32` and `Int64` go through
`IntegerInstanceTestsFn`, `Word32` and `Word64` through
`WordInstanceTestsFn`, `Real32` through `RealInstanceTestsFn`, and the int and
real sequences through the same `MonoVectorTestsFn` and friends the required
`Char` and `Word8` sequences use. What needed writing is the surface they add:

- `src/optional/test-int-inf.sml` — the part of `INT_INF` that `INTEGER` does
  not describe. Unboundedness itself, `divMod`, `quotRem`, `log2`, `pow`
  including the five cases the specification fixes at a negative exponent, and
  the bitwise operations, which work on the *infinite* two's complement
  representation and so are not a fixed-width word's: `andb (~2, 3)` is `2`
  and `notb i` is `~(i+1)`, at any magnitude.
- `src/optional/gen-pack-word.sml` — generic over `PACK_WORD`, applied to all
  six `PackWordNBig`/`PackWordNLittle` structures. The element width is read
  from `bytesPerElem`, so the same body tests a two-byte and an eight-byte
  element; what the instantiation declares is the byte order the structure's
  name promises, since `isBigEndian` is exactly what a byte-order bug gets
  wrong.
- `src/optional/gen-pack-real.sml` — generic over `PACK_REAL`, applied to the
  big-endian and little-endian structures *together*. One structure alone
  cannot be asked whether it got the byte order right without assuming a
  particular float format; the pair can, because whatever the format, the two
  must lay the same value down in opposite orders.
- `src/optional/test-array2.sml` — `ARRAY2`. Mostly about the two things that
  distinguish it from `Array`: the traversal argument, whose effect is
  observable through `fold` over a non-commutative operator, and the region,
  where `NONE` means "to the edge" and `SOME 0` means "nothing at all".

**Still not covered**, and deliberately so: `Posix`, `Unix`, `Windows`,
`Socket`, `NetHostDB` and the rest of the system interface, `BoolVector` and
`BoolArray`, `MONO_ARRAY2`, and the `Wide*` family. Adding one means a file
under `src/optional/`, a line in `build/optional/<impl>.txt` and a line in
`src/optional/opt-<impl>.sml`.

## Layout

```
src/framework/   random, generators, printers, assertions, test tree, runner
src/config/      TEST_CONFIG, the shipped configurations, and the selection
src/tests/       one functor over TEST_CONFIG per required Basis structure
                 (35 files), including gen-*.sml, generic over a signature and
                 applied to every required instance
src/optional/    tests for the optional structures, and one opt-*.sml profile
                 per implementation saying which of them that build names
src/main.sml     command line entry point
build/           sources.txt, optional/<impl>.txt, and the six build
                 descriptions generated from them
run/             one script per implementation
tools/           gen-builds.sh, the member inventories, and the coverage checker
```

## Results on three implementations

Run at the defaults. These are what the suite reports, with the reading of the
specification that each test encodes; where the Basis genuinely permits either
behaviour the test accepts both, or is gated by configuration.

| | tests | passed | failed | errored | skipped |
| --- | --- | --- | --- | --- | --- |
| SML/NJ 2026.1 (63-bit int and word) | 1756 | 1724 | 27 | 0 | 5 |
| MLton 20241230 (32-bit int and word) | 1882 | 1875 | 2 | 0 | 5 |
| Poly/ML 5.7.1 (63-bit int and word) | 1731 | 1714 | 8 | 4 | 5 |

The required part is 1299 tests in every column. The columns differ because
each implementation's profile names a different set of optional structures:
583 further tests on MLton, 457 on SML/NJ, 432 on Poly/ML. Running any of the
three with `--core` gives the same 1299 everywhere, plus one skip standing for
the optional group that build does not have.

"Errored" means an unexpected exception escaped, as opposed to an assertion
returning false; the two are counted separately so that a library raising
something surprising is never mistaken for a test simply being false. The five
skips are the three Windows `OS.Path` tests, the hexadecimal real literal
test, and the combined-direction poll test described below.

**SML/NJ 2026.1** — 21 failures in the required part, from nine distinct
defects:

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

and 6 more in the optional structures, from four:

- `IntInf.pow (1, ~5)` is `0`. The specification fixes `pow` at a negative
  exponent by cases: a zero base raises `Div`, a base of absolute value one
  gives `i^j` — so `1` for `1`, and `1` or `~1` by parity for `~1` — and only
  a base larger than one truncates to `0`. SML/NJ takes the last case for all
  of them.
- `IntInf.fmt StringCvt.HEX` emits lower-case digits. `IntInf` and `LargeInt`
  are the same structure here, so this is the `LargeInt` defect above showing
  up a second time.
- `Array2.array (0, 3, init)` has dimensions `(0, 0)`: a zero in one dimension
  erases the other, although `array (r, c, init)` is specified to build an
  `r` by `c` array. MLton reports `(0, 3)`.
- An `Array2` region with `nrows = SOME 0` is traversed to the edge of the
  array as though the extent had been `NONE`, so an empty region is not empty.
  `SOME 0` and `NONE` are different requests. This accounts for two of the
  six, the unit test and the property.
- `RealVector.update` performs no bounds check, the same immutable-update
  defect already listed for `Vector`, `CharVector` and `Word8Vector`.

**MLton 20241230** — 2 failures, both in the required part; every optional
structure it provides passes:

- `Bool.fromString "   true"` is `NONE`; leading whitespace is not skipped,
  though `Int.fromString "   42"` correctly returns `SOME 42`.
- `TextIO.endOfStream` stays `false` after `inputAll` has consumed the whole
  stream. Draining the same stream with `input1` sets it correctly.

**Poly/ML 5.7.1** — 6 failures in the required part:

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

and 6 more in the optional structures, from two:

- `Word64` and `SysWord` repeat the two `LargeWord` defects above, `fromInt ~1`
  and `~>>` past the full width. All three are the same 64-bit structure under
  three names, so each defect is reported three times.
- `Array2.nCols` raises `Subscript` for an array with no rows: both
  `array (0, 3, init)` and `fromList []` have zero rows, and asking either for
  its column count raises rather than answering `3` and `0`. `nRows` of an
  array with no columns is fine, so only the one direction is affected.

Poly/ML 5.7.1 dates from 2018 and is what Ubuntu ships; a current release may
behave differently.

## Continuous integration

`.github/workflows/conformance.yml` installs the three implementations that
can build the suite from a binary — MLton and Poly/ML from Ubuntu, SML/NJ from
the openSUSE Build Service repository that packages it for Debian and Ubuntu —
runs the suite on each, and publishes a Markdown report as the job summary and
as an artifact. Nothing is built from source; compiling any of the three would
take longer than the test run does.

It runs on demand only — "Run workflow" in the Actions tab, taking the seed
and the trial count as inputs. Its output is a report to be read rather than a
signal to be watched, and a full run costs three compilers' worth of building
the suite.

Two scripts do the work, and both are usable outside CI:

```sh
tools/ci-run.sh mlton out --trials 100   # build, run, record the outcome
tools/ci-report.sh out > report.md       # turn the logs into one report
```

`ci-run.sh` records an implementation's outcome without letting it stop the
ones after it, so a compiler that cannot build the suite still leaves a full
report for the others. It classifies a run by whether it reached its tally
line rather than by exit status, because "this implementation has 27
conformance defects" and "this compiler rejected the source" are different
events that a single exit code cannot tell apart.

The workflow follows that division. A failing test does not fail it: the suite
exists to find defects in the implementations it runs on, and every one of
them has some, so a red build every time would say nothing. A compiler that
cannot build the suite does fail it, since then nothing was learned.

**MLKit is not in the run.** With `src/compat/compat-mlkit.sml` supplying the
seven required members it lacks, MLKit 4.7.22 type-checks the whole suite —
every one of the 992 required members resolves — but its back end then dies
with `Impossible: CompileDec.succeed` while compiling the program. That is an
internal compiler error, not a missing member: it reproduces with
`src/main.sml` exactly as committed, does not reproduce in any smaller program
built out of the same code, and none of `-no_opt`, `-no_aopt` or
`-no_cross_opt` avoids it. There is no run to report, so CI does not attempt
one. `run/mlkit.sh` and `tools/ci-run.sh` still know how, for whenever that is
fixed.
