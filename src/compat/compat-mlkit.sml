(* The Basis members MLKit does not provide, supplied so the suite compiles.
 *
 * MLKit 4.7.22 is missing seven required members: String.scan,
 * Real.toDecimal, Real.fromDecimal, the LargeReal pair of those, and
 * Timer.checkCPUTimes and Timer.checkGCTime.  Every other one of the 992 in
 * tools/required-members.txt is present.  A whole-program compiler stops at
 * the first unbound identifier, so without this file MLKit runs none of the
 * suite rather than failing seven tests of it.
 *
 * Each definition below delegates to MLKit wherever MLKit has something to
 * delegate to, so that what is being tested stays MLKit's code and not this
 * suite's.  The exception is the collector accounting, which cannot be
 * delegated because there is nothing to delegate to -- see below.
 *
 * The tests of all seven are skipped rather than run.  A conformance suite
 * that supplies a member itself and then reports a pass for it is worse than
 * one that does not run at all; the names are listed in Compat.substituted,
 * the tests that exercise them consult it, and the run header prints them.
 *)

structure Compat =
  struct
    val substituted : string list =
      [ "String.scan"
      , "Real.toDecimal", "Real.fromDecimal"
      , "LargeReal.toDecimal", "LargeReal.fromDecimal"
      , "Timer.checkCPUTimes", "Timer.checkGCTime"
      ]
    fun isSubstituted name = List.exists (fn n => n = name) substituted
  end

(* String.scan is Char.scan applied until it declines: a string element is a
 * character element, and that is the whole of the definition.  Nothing about
 * escape sequences, the \...\ gap or the numeric forms is decided here; all
 * of it stays with MLKit's own Char.scan.
 *
 * The loop returns the stream from before the scan that declined, so scanning
 * stops at the first thing it cannot read and leaves it unread.  It never
 * returns NONE: an input from which no element can be read yields the empty
 * string, which is what makes `String.fromString ""` SOME "". *)
structure String =
  struct
    open String

    fun scan getc src =
      let
        fun loop (src, acc) =
          case Char.scan getc src of
              SOME (c, src') => loop (src', c :: acc)
            | NONE => SOME (implode (List.rev acc), src)
      in
        loop (src, [])
      end
  end

(* The generic tests in src/tests/gen-numeric.sml take their instance as
 * `structure R : REAL`, so the members have to be added to the signature as
 * well as to the structures: a structure matched against MLKit's REAL loses
 * anything that signature does not mention. *)
signature REAL =
  sig
    include REAL
    val toDecimal : real -> IEEEReal.decimal_approx
    val fromDecimal : IEEEReal.decimal_approx -> real option
  end

(* toDecimal and fromDecimal, through the text forms of the same values.
 *
 * MLKit has Real.fmt, Real.fromString, Real.class, Real.signBit and all of
 * IEEEReal, so the digits and the exponent can be got by writing the value
 * out exactly and reading it back as a decimal approximation -- MLKit's own
 * formatting and MLKit's own scanner at both ends.  The class does not
 * survive that trip, since a scanner cannot tell a subnormal from a normal
 * value, so it is taken from Real.class directly, and the sign from
 * Real.signBit, which is the only way to keep the sign of a negative zero.
 *
 * The result is no more accurate than the implementation's own text
 * conversions, which is the reason the tests of these are skipped and not
 * merely expected to pass. *)
structure Real =
  struct
    open Real

    fun toDecimal x =
      let
        val fallback = { class = class x, sign = signBit x,
                         digits = [] : int list, exp = 0 }
      in
        case IEEEReal.fromString (fmt StringCvt.EXACT x) of
            NONE => fallback
          | SOME d => { class = class x, sign = signBit x,
                        digits = #digits d, exp = #exp d }
      end

    fun fromDecimal d = fromString (IEEEReal.toString d)
  end

structure LargeReal =
  struct
    open LargeReal

    fun toDecimal x =
      let
        val fallback = { class = class x, sign = signBit x,
                         digits = [] : int list, exp = 0 }
      in
        case IEEEReal.fromString (fmt StringCvt.EXACT x) of
            NONE => fallback
          | SOME d => { class = class x, sign = signBit x,
                        digits = #digits d, exp = #exp d }
      end

    fun fromDecimal d = fromString (IEEEReal.toString d)
  end

(* The collector accounting is the one thing here that is invented rather than
 * delegated.  MLKit exposes no garbage collection times at all, so there is
 * nothing to split the interval with: checkGCTime reports zero and
 * checkCPUTimes puts the whole of checkCPUTimer under `nongc`.  That is a
 * stub, not an implementation, and the tests of both are skipped -- reporting
 * a pass for a fabricated zero would be the worst outcome available. *)
structure Timer =
  struct
    open Timer

    fun checkGCTime (_ : cpu_timer) = Time.zeroTime

    fun checkCPUTimes t =
      let
        val { usr, sys } = checkCPUTimer t
      in
        { nongc = { usr = usr, sys = sys },
          gc = { usr = Time.zeroTime, sys = Time.zeroTime } }
      end
  end
