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

`run/mlton.sh` passes `-drop-pass bounceVars`. That is not a tuning
preference: MLton compiles the suite as one program, and `bounceVars` — an
RSSA pass whose cost grows with the size of a single function — needs more
than 7GB on the function that builds the test tree, so the compiler is killed
on an ordinary machine and on a GitHub runner alike. Dropping that one pass
costs a little generated code quality and nothing else.

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
| `canExtractAtHugeIndex` | `String.extract` may be called with an index near `maxInt` |
| `negativeSleepReturns` | `OS.Process.sleep` returns at once on a negative time |
| `dateFmtHandlesZone` | `Date.fmt` is safe to call with `%Z` |
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

Four of those flags are a different kind of thing, and all four default to
off: `canPollBothDirections`, `canExtractAtHugeIndex`, `negativeSleepReturns`
and `dateFmtHandlesZone` each guard a call that the Basis specifies plainly
but that one of the three implementations does not merely get wrong — it
crashes the runtime or blocks forever, and a run that dies reports nothing
about the thousand tests it never reached. Each is written up under the
implementation it belongs to below. Turning one on asks the suite to make the
call; leaving it off reports a skip with the reason, which is the same
treatment every other inapplicable test gets.

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

1778 tests at run time, from 1512 in the source: 884 unit tests and 628
properties, some of which are generic over a signature and instantiated once
per required instance — 794 properties actually run. At the default 100 trials
that is about 79,000 generated cases. The optional structures below add 116
more tests in the source and, on MLton's profile, 741 at run time and another
41,000 generated cases.

Eight of those structures are monomorphic sequences, three are `WORD`
instances, three are `INTEGER` and two are `REAL`. Testing each by hand would
be the same file copied fourteen times, so the tests for those are written
once against the signature (`gen-mono-seq.sml`, `gen-mono-slice.sml`,
`gen-numeric.sml`) and applied to every instance in `test-instances.sml`. The
hand-written `Word`, `Int` and `Real` suites remain and go deeper on the
default types; the generic ones give breadth across all the instances.

### What a test encodes

A member being *mentioned* somewhere is not the same as its behaviour being
checked, so the tests are written against the specification clause by clause:
what a function returns, which exception it raises and on which argument, and
what order it promises to do things in. Four kinds of text in the Basis are
turned into tests mechanically.

**The tables are transcribed.** `Char.toString` and `Char.toCString` are
specified by a table of escape sequences; both tables are written out as a
reference function and checked against every character, not against a sample.
The same goes for the `Math` tables of exceptional cases — every row of
`atan2`'s eleven and `pow`'s eighteen, and the properties given for `sinh`,
`cosh` and `tanh` at zero and at the infinities.

**The worked examples are tests.** Where the specification illustrates a
function with a table of inputs and results — `OS.Path.fromString`,
`getParent`, `splitDirFile`, `splitBaseExt` and `mkRelative`,
`Char.fromString` and `String.fromString`, `Substring.splitl`/`splitr`,
`String.tokens`/`fields`, `Date`'s `minute = 10, second = ~140`, `Time`'s
`fmt 0 (fromReal 1.8) = "2"` — that table is the test.

**"Equivalent to" is a property.** The Basis defines many operations by
giving an equivalent expression: `mapPartial f` is `((map valOf) o (filter
isSome) o (map f))`, `app f sl` is `appi (f o #2) sl`, `toString` is `fmt
(GEN NONE)`, `skipWS` is `dropl Char.isSpace`, `Array.vector` is
`Vector.tabulate (length arr, fn i => sub (arr, i))`, `fromInt` is
`fromLargeWord o LargeWord.fromLargeInt o Int.toLarge`. Each such equivalence
is a property over generated inputs rather than a comment.

**The Discussion is part of the specification.** `STREAM_IO`'s discussion
states its invariants as SML predicates — `chkInput`, `chkClose`, `noBlock`,
`isEOS`, `allAndN`, `input1` in terms of `inputN` — and they are tested as
written. So are `SUBSTRING`'s requirement that `splitl`, `tokens` and the rest
return pieces sharing the base string, `LIST_PAIR`'s requirement that the
length check be made lazily, `CHAR`'s locale-independent definition of every
predicate as a range test, `INT_INF`'s rule that a high enough bit reports the
sign, and `WORD`'s requirement that `LargeWord.wordSize <= LargeInt.precision`.

Where the specification contradicts itself the test accepts both readings and
says which passage it is reconciling: `Math.cosh` at a negative infinity is
`+inf` by the definition given in the same paragraph and `~inf` by the table
below it; a closed `PrimIO` reader raises `ClosedStream` by the `PRIM_IO`
description and `Io` carrying `ClosedStream` by the `IO` discussion; `Time`'s
scanning grammar makes the point optional in one reading and mandatory in
another. Accepting both is not a weakening — it is the only honest reading of
a document that says both things.

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

A handful of specified behaviours cannot be reached from inside a running
test, and are left out deliberately rather than approximated: the `Size`
raised when a string, vector or array would exceed `maxSize` or `maxLen`
(provoking it means asking for an allocation of that size); `Real.fromInt` of
a value whose magnitude exceeds `maxFinite` (no integer type on these
implementations is that wide); the order in which `OS.Process.atExit` actions
run, and `exit` and `terminate` themselves, all of which are observable only
after the run has ended; `OS.FileSys.fileId p = fileId (readLink p)`, which
needs a symbolic link the Basis gives no way to create; and the actual
buffering behaviour behind `IO.NO_BUF`, `LINE_BUF` and `BLOCK_BUF`, of which
only the flushing that `flushOut` and `setBufferMode` promise is observable.

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
| SML/NJ 2026.1 (63-bit int and word) | 2359 | 2295 | 56 | 0 | 8 |
| MLton 20241230 (32-bit int and word) | 2519 | 2503 | 8 | 0 | 8 |
| Poly/ML 5.7.1 (63-bit int and word) | 2353 | 2312 | 29 | 4 | 8 |

The required part is 1778 tests in every column. The columns differ because
each implementation's profile names a different set of optional structures:
741 further tests on MLton, 581 on SML/NJ, 575 on Poly/ML. Running any of the
three with `--core` gives the same 1778 everywhere, plus one skip standing for
the optional group that build does not have.

"Errored" means an unexpected exception escaped, as opposed to an assertion
returning false; the two are counted separately so that a library raising
something surprising is never mistaken for a test simply being false. The
eight skips are the three Windows `OS.Path` tests, the hexadecimal real
literal test, and the four tests behind the crash-guard flags: the
combined-direction poll, `String.extract` at a huge index, the negative sleep,
and `Date.fmt "%Z"`.

**MLton 20241230** — 8 failures, all in the required part; every optional
structure it provides passes:

- `Bool.scan` neither skips leading whitespace nor ignores case, although the
  specification asks for both: `Bool.fromString "   true"` and
  `Bool.fromString "TRUE"` are `NONE`. `Int.fromString "   42"` skips
  whitespace correctly, so this is specific to `Bool`. Three of the eight.
- `Char.fromCString` and `String.fromCString` accept an unescaped double
  quote, which the specification singles out as the one character C does not
  allow bare: `Char.fromCString "\""` should be `NONE` and
  `String.fromCString "a\"b"` should stop at the quote and return `SOME "a"`.
- `TextIO.endOfStream` stays `false` after `inputAll` has consumed the whole
  stream. Draining the same stream with `input1` sets it correctly.
- `Date.date` with an offset larger than a day reduces it the wrong way. The
  specification writes the reduction out: an offset of 25 hours becomes an
  offset of 1 hour with 24 hours added to the date. MLton reports an offset of
  23 hours.
- `TextIO.StreamIO.canInput` reports `SOME 0` on a stream that has already
  been determined by a call to `input` — the `STREAM_IO` discussion states as
  an invariant that `SOME 0` means end-of-stream, and this stream has a
  character available.

**SML/NJ 2026.1** — 48 failures in the required part and 8 in the optional
structures. The distinct defects:

- `String.isSubstring "" ""` is `false`. The empty string is a substring of
  every string; `isSubstring "" "a"` and `isPrefix "" ""` are both `true`.
  Four of the failures, counting the laws that follow from it.
- The scanners skip only space, tab and newline as whitespace. `\r`, `\f` and
  `\v` are left in place by `StringCvt.skipWS` and by every scanner built on
  it, although `Char.isSpace` reports all six as whitespace.
- `Vector.update`, `CharVector.update`, `Word8Vector.update` and
  `RealVector.update` perform no bounds check: index `3` and index `~1` on a
  three-element vector both return normally instead of raising `Subscript`.
  The array versions are checked correctly, so this is specific to the
  immutable update.
- `TextIO.inputAll` and `BinIO.inputAll` raise `Io` on an empty stream. This
  reaches the functional `StreamIO` layer too, which is where most of the
  remaining failures come from.
- `inputN` with a negative count raises `Subscript` where the specification
  says `Size`, at all three levels — `TextIO`, `BinIO` and
  `TextIO.StreamIO`.
- `TextIO.StreamIO.getReader` can be applied twice. The second call must raise
  `Io`: the stream is truncated by the first.
- `exnMessage Div` is `"divide by zero"`. The specification allows any wording
  but requires the message to contain `exnName ex`, and this one does not
  contain `"Div"`.
- `Bool.fromString "TRUE"` is `NONE`; the specification says the scan ignores
  case.
- `Char.fromCString "\^H"` is `NONE`: the control escape `\^c` is in the C
  escape table the specification lists. `fromCString` also accepts an
  unescaped double quote, as MLton's does.
- `Char.scan` leaves an escaped formatting sequence in the remainder. The
  specification requires that the stream returned by `scan` never has one as
  its prefix, since such sequences are scanned and passed over.
- `String.fromString "\ \\^D"` is `NONE` rather than `SOME ""`. The
  specification tabulates this case: a prefix that scans to nothing is still a
  successful scan.
- `Real.rem (inf, 3.0)` is `0.0`; an infinite dividend gives NaN.
- The signed zero is lost in several `Math` functions: `sinh ~0.0` is `+0.0`,
  `atan2 (~0.0, 1.0)` is `+0.0`, and `pow (~0.0, ~3.0)` is `+inf`, where the
  tables give `~0.0`, `~0.0` and `~inf`. `atan2 (inf, inf)` is not `pi/4`.
- `Math.pow` has a relative error of about 1e-10 (roughly 184,000 ulps) for
  non-trivial exponents, and `sinh` and `cosh` disagree with their own
  definition in terms of `exp` by more than the configured tolerance. The
  Basis mandates no accuracy for these, so both are quality observations
  rather than conformance failures — they are what the laws report at the
  default 4096-ulp tolerance, and raising `mathToleranceUlps` silences them.
- `Date.fromString` does not skip leading whitespace, though every other
  scanner in the implementation does.
- `Date.toTime` ignores the offset of a date carrying an explicit one, so no
  such date round-trips through a time and two dates in different zones
  compare as the same instant. `Date.date` also reduces an offset larger than
  a day without moving the borrowed hours into the date.
- `LargeInt.fmt StringCvt.HEX` emits lower-case digits while `Int.fmt`,
  `Word.fmt`, `LargeWord.fmt` and `Position.fmt` all emit upper case. The same
  structure appears again as `IntInf`, so the defect is reported three times.
- `LargeWord.toInt`, `Word64.toInt` and `SysWord.toInt` disagree with the
  composition the `WORD` discussion writes out,
  `Int.fromLarge o LargeWord.toLargeInt o toLarge`.
- `IntInf.pow (1, ~5)` is `0`. The specification fixes `pow` at a negative
  exponent by cases: a zero base raises `Div`, a base of absolute value one
  gives `i^j` — so `1` for `1`, and `1` or `~1` by parity for `~1` — and only
  a base larger than one truncates to `0`. SML/NJ takes the last case for all
  of them.
- `Array2.array (0, 3, init)` has dimensions `(0, 0)`: a zero in one dimension
  erases the other. An `Array2` region with `nrows = SOME 0` is traversed to
  the edge of the array as though the extent had been `NONE`, so an empty
  region is not empty.
- Two calls crash or hang rather than answering, so both are behind
  configuration flags and are skipped by default. `String.extract ("abcde",
  valOf Int.maxInt, SOME 1)` dies with `Fatal error -- bogus overflow fault`,
  where the specification requires the bounds check to raise `Subscript`
  without an overflowing addition — the same call on `substring` and on every
  `Substring` operation is checked correctly. `OS.Process.sleep` with a
  negative argument never returns, where the specification says the process
  does not sleep at all. `OS.IO.poll` **terminates the runtime with a
  segmentation fault** when a single poll descriptor carries both `pollIn` and
  `pollOut`; each direction alone is fine.

**Poly/ML 5.7.1** — 20 failures in the required part (four of them errors) and
13 in the optional structures:

- `Real.fromString` rejects `"inf"`, `"infinity"` and `"nan"`, which are in
  the Basis grammar and which its own `Real.toString` produces, so the special
  values do not round-trip.
- `Real.nextAfter (inf, 1.0)` does not return an infinity; the specification
  says `nextAfter` of `+-infinity` is `+-infinity`.
- `IEEEReal.fromString "0.005"` reports `digits = [0,0,5]` and `exp = 0`. The
  specification strips the leading zeros of the fraction and lowers the
  exponent instead: `digits = [5]` and `exp = ~2`.
- `Substring.substring ("abcde", valOf Int.maxInt, 1)` raises `Overflow`. The
  implementation note for these functions requires the bounds check to be done
  in a way that cannot overflow; `String.substring` is correct.
- `Char.scan` leaves an escaped formatting sequence in the remainder, and both
  `Char.fromCString` and `String.fromCString` accept an unescaped double
  quote, exactly as SML/NJ does.
- `Math.pow (1.0, inf)` is `1.0`. The specification's table gives NaN for
  `+-1` raised to `+-infinity`; C99 gives `1.0`, and Poly/ML follows C.
  MLton follows the table.
- `Time.fmt ~1` returns a string instead of raising `Size`, and
  `Time.toSeconds` rounds towards negative infinity rather than towards zero,
  so `~1500` milliseconds becomes `~2` seconds instead of `~1`.
- `OS.Path.mkRelative` accepts a relative `relativeTo` argument instead of
  raising `Path`. `mkAbsolute` rejects it correctly.
- `Date.fmt ""` raises `Date`. An empty format string should produce an empty
  string, as it does on the other two. The same defect makes `Date.fmt "%Z"`
  raise for a date with an explicit offset — and that call does not merely
  raise: it corrupts the heap, and the run dies with a segmentation fault
  several tests later. It is behind `dateFmtHandlesZone` for that reason.
- `OS.Process.sleep` raises `SysErr` on a negative time, where the
  specification says it returns immediately without sleeping. That one is only
  visible with `negativeSleepReturns` turned on, since the same test hangs
  SML/NJ.
- `LargeWord.fromInt ~1` yields `7FFFFFFFFFFFFFFF` rather than all ones, even
  though `LargeWord.wordSize` is 64 and `LargeWord.notb 0w0` and
  `LargeWord.- (0w0, 0w1)` both correctly give `FFFFFFFFFFFFFFFF`.
- `Word8.toLargeX` does not sign-extend into the top bit: `0wxFF` becomes
  `7FFFFFFFFFFFFFFF` instead of `FFFFFFFFFFFFFFFF`. `Word.toLargeX` is
  correct, so only the narrower source width is affected.
- `LargeWord.~>> (0w1, 0w64)` yields `1` rather than `0`; shifting a positive
  value right by the full word width must clear it. `LargeWord.>>` handles the
  same case correctly.
- `LargeWord.toInt` of the top bit returns a value instead of raising
  `Overflow`, and the conversions disagree with the compositions through
  `LargeWord` and `LargeInt` that the `WORD` discussion writes out. `Word64`
  and `SysWord` are the same structure under other names, so each of these
  four defects is reported three times.
- `PackRealBig.subVec` reads a vector shorter than one element instead of
  raising `Subscript`.
- `Array2.nCols` raises `Subscript` for an array with no rows: both
  `array (0, 3, init)` and `fromList []` have zero rows, and asking either for
  its column count raises rather than answering `3` and `0`. `nRows` of an
  array with no columns is fine, so only the one direction is affected.
- Separately, 5.7.1 cannot compile `Vector.sub` or `Array.sub` applied to a
  constant sequence at a negative constant index. That is worked around by
  `Assert.hide` rather than by dropping the tests.

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
