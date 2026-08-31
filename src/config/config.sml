(* config.sml -- everything the Basis leaves to the implementation.
 *
 * The rule this file follows: if a fact can be *read* from the Basis itself
 * (Int.precision, Word.wordSize, Char.maxOrd, Real.radix, String.maxSize, ...)
 * then the tests read it and no configuration is needed.  What lives here is
 * only what cannot be discovered from inside the language -- and, crucially,
 * what should not be discovered, because the whole point of a conformance
 * suite is to compare the implementation against a *declaration* of intended
 * behaviour rather than against itself.
 *
 * Porting to a new system means writing one structure matching TEST_CONFIG
 * and pointing the build file at it.  Nothing else in the suite changes.
 *)

structure PathStyle =
  struct
    datatype style = UNIX | WINDOWS
  end

signature TEST_CONFIG =
  sig
    (* Reported in the run header; not otherwise used. *)
    val implName : string

    (* --- reals ------------------------------------------------------- *)

    (* Real is an IEEE 754 binary format with the usual special values.  When
     * false, every test that mentions an infinity, a NaN or a negative zero
     * is skipped rather than reported as a failure. *)
    val hasIEEEReals : bool

    (* Zero is signed and Real.signBit distinguishes 0.0 from ~0.0. *)
    val hasSignedZero : bool

    (* Subnormal values exist and Real.class reports them as SUBNORMAL. *)
    val hasSubnormals : bool

    (* IEEEReal.setRoundingMode actually changes the rounding of arithmetic.
     * Many implementations accept the call and ignore it. *)
    val hasRoundingModes : bool

    (* Real.fromString accepts the hexadecimal form "0x1.8p3".  This is an
     * extension: the Basis grammar for scanning reals has no hexadecimal
     * form, so the default is false and turning it on tests an extra
     * guarantee the implementation chooses to make. *)
    val realFromStringAcceptsHex : bool

    (* How far the transcendental functions in Math may stray from the
     * correctly rounded result, in units in the last place.  The Basis
     * requires no particular accuracy, so a suite that hard-codes a tolerance
     * is testing its author's machine rather than the specification. *)
    val mathToleranceUlps : int

    (* --- characters -------------------------------------------------- *)

    (* Char.isAlpha and friends are false for every character above 127.  The
     * Basis fixes their behaviour only on the ASCII range; above it the
     * result is locale- or implementation-defined. *)
    val charPredicatesAreAscii : bool

    (* --- integers ---------------------------------------------------- *)

    (* Arithmetic on the default int raises Overflow rather than wrapping.
     * The Definition requires this, so a false here documents a known
     * deviation rather than a permitted choice. *)
    val intOverflowRaises : bool

    (* --- operating system -------------------------------------------- *)

    val pathStyle : PathStyle.style

    (* OS.FileSys and file-backed TextIO/BinIO can be exercised. *)
    val hasFileSystem : bool

    (* A directory the suite may create and delete files in.  Only consulted
     * when hasFileSystem is true. *)
    val scratchDir : string

    (* OS.Process.getEnv returns real answers. *)
    val hasProcessEnv : bool

    (* The host has symbolic links, so OS.FileSys.isLink and readLink mean
     * something.  Nothing in the required Basis can create one, so the tests
     * only inspect links the suite finds. *)
    val hasSymbolicLinks : bool

    (* OS.Process.system can run a child process.  Sandboxes and hosted
     * implementations frequently cannot. *)
    val canSpawnProcesses : bool

    (* OS.IO.poll works on descriptors obtained from ordinary files. *)
    val hasPollingIO : bool

    (* A single poll descriptor may carry both pollIn and pollOut.  This is
     * separate from hasPollingIO because SML/NJ 2026.1 does not merely refuse
     * the combination -- it terminates the runtime with a segmentation fault,
     * which would take the rest of the run down with it.  The default is
     * therefore off, and the individual directions are tested regardless. *)
    val canPollBothDirections : bool

    (* --- strings ----------------------------------------------------- *)

    (* String.extract may be called with an index close to Int.maxInt.  The
     * Basis requires the bounds check to raise Subscript without going
     * through an overflowing addition, so this ought to be an ordinary test;
     * it is behind a flag because SML/NJ 2026.1 does not raise anything -- it
     * dies with "Fatal error -- bogus overflow fault", taking the rest of the
     * run with it.  The same check on substring and on the Substring
     * operations is safe everywhere and is made unconditionally. *)
    val canExtractAtHugeIndex : bool

    (* OS.Process.sleep returns immediately when given a zero or negative
     * time, as the specification requires.  Behind a flag because SML/NJ
     * 2026.1 does not return at all for a negative argument: the process
     * blocks forever and the run has to be killed, which is worse than a
     * crash.  A zero sleep is tested unconditionally. *)
    val negativeSleepReturns : bool

    (* --- dates ------------------------------------------------------- *)

    (* Date.fmt is safe to call with the time-zone directive "%Z".  This is
     * separate from the rest of Date because Poly/ML 5.7.1 does not merely
     * get it wrong -- formatting "%Z" for a date carrying an explicit offset
     * corrupts the heap and the run dies with a segmentation fault some time
     * later, taking every remaining test with it.  The default is therefore
     * off; every other directive is tested regardless. *)
    val dateFmtHandlesZone : bool

    (* --- time -------------------------------------------------------- *)

    (* The granularity of Time.time, in nanoseconds.  The Basis fixes the
     * units of the conversion functions but not the resolution of the
     * underlying representation, so an implementation that keeps microseconds
     * is conforming and simply cannot round-trip a nanosecond count. *)
    val timeResolutionNanos : int
  end

(* A configuration for a conforming implementation on a Unix-like host.
 * This is what the provided build files select. *)
structure ConfigUnix : TEST_CONFIG =
  struct
    val implName = "conforming implementation, Unix host"

    val hasIEEEReals = true
    val hasSignedZero = true
    val hasSubnormals = true
    val hasRoundingModes = true
    val realFromStringAcceptsHex = false
    val mathToleranceUlps = 4096

    val charPredicatesAreAscii = true

    val intOverflowRaises = true

    val pathStyle = PathStyle.UNIX
    val hasFileSystem = true
    val scratchDir = "scratch"
    val hasProcessEnv = true
    val hasSymbolicLinks = true
    val canSpawnProcesses = true
    val hasPollingIO = true
    val canPollBothDirections = false

    val canExtractAtHugeIndex = false
    val negativeSleepReturns = false
    val dateFmtHandlesZone = false

    val timeResolutionNanos = 1000
  end

structure ConfigWindows : TEST_CONFIG =
  struct
    open ConfigUnix
    val implName = "conforming implementation, Windows host"
    val pathStyle = PathStyle.WINDOWS
  end

(* The most conservative setting: assume nothing beyond what the Definition
 * requires.  Useful when bringing up a new or partial implementation, since
 * everything optional is switched off and only the mandatory core is tested. *)
structure ConfigMinimal : TEST_CONFIG =
  struct
    open ConfigUnix
    val implName = "minimal assumptions"
    val hasIEEEReals = false
    val hasSignedZero = false
    val hasSubnormals = false
    val hasRoundingModes = false
    val realFromStringAcceptsHex = false
    val hasFileSystem = false
    val hasProcessEnv = false
    val hasSymbolicLinks = false
    val canSpawnProcesses = false
    val hasPollingIO = false
    val canPollBothDirections = false
    val canExtractAtHugeIndex = false
    val negativeSleepReturns = false
    val dateFmtHandlesZone = false
  end
