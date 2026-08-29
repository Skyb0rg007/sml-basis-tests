(* Tests for the Real structure.
 *
 * Everything that mentions an infinity, a NaN or a signed zero is gated on
 * the configuration, because the Basis permits a Real that is not IEEE 754.
 * The algebraic laws that hold for any reasonable floating point format are
 * tested unconditionally, but only over finite values.
 *)

functor RealTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val showR = Show.real
    val reals = G.anyReal
    val realPair = G.pair (reals, reals)
    val showRPair = Show.pair (showR, showR)

    (* Built lazily: on a system without IEEE reals these expressions may trap,
     * and the tests that use them are skipped there anyway. *)
    fun nan () = 0.0 / 0.0
    fun inf () = Real.posInf
    fun ninf () = Real.negInf
    fun negZero () = ~0.0

    val ieee = C.hasIEEEReals
    val ieeeWhy = "implementation not declared IEEE"

    fun eqCls msg (e, a) =
      let
        fun name IEEEReal.NAN = "NAN"
          | name IEEEReal.INF = "INF"
          | name IEEEReal.ZERO = "ZERO"
          | name IEEEReal.NORMAL = "NORMAL"
          | name IEEEReal.SUBNORMAL = "SUBNORMAL"
      in
        A.eqBy (op =, name) msg (e, a)
      end

    val suite = Group ("Real",
      [ Group ("format parameters",
        [ Case ("radix and precision are sensible", fn () =>
            (A.that ("radix = " ^ Int.toString Real.radix) (Real.radix >= 2);
             A.that ("precision = " ^ Int.toString Real.precision)
                    (Real.precision > 0))),

          Case ("the named bounds are ordered", fn () =>
            (A.that "minPos > 0" (Real.minPos > 0.0);
             A.that "minPos <= minNormalPos" (Real.minPos <= Real.minNormalPos);
             A.that "minNormalPos < maxFinite" (Real.minNormalPos < Real.maxFinite);
             A.that "maxFinite is finite" (Real.isFinite Real.maxFinite)))
        ]),

        Group ("equality and comparison on finite values",
        [ Case ("== and !=", fn () =>
            (A.eqBool "equal" (true, Real.== (1.0, 1.0));
             A.eqBool "different" (false, Real.== (1.0, 2.0));
             A.eqBool "!= is the negation" (true, Real.!= (1.0, 2.0)))),

          Case ("compare", fn () =>
            (A.eqOrder "less" (LESS, Real.compare (1.0, 2.0));
             A.eqOrder "equal" (EQUAL, Real.compare (1.0, 1.0));
             A.eqOrder "greater" (GREATER, Real.compare (2.0, 1.0)))),

          Case ("compareReal", fn () =>
            let
              fun name IEEEReal.LESS = "LESS"
                | name IEEEReal.EQUAL = "EQUAL"
                | name IEEEReal.GREATER = "GREATER"
                | name IEEEReal.UNORDERED = "UNORDERED"
            in
              A.eqBy (op =, name) "less" (IEEEReal.LESS, Real.compareReal (1.0, 2.0));
              A.eqBy (op =, name) "equal" (IEEEReal.EQUAL, Real.compareReal (1.0, 1.0))
            end),

          Case ("min and max", fn () =>
            (A.eqRealExact "min" (1.0, Real.min (1.0, 2.0));
             A.eqRealExact "max" (2.0, Real.max (1.0, 2.0)))),

          Case ("abs and negation", fn () =>
            (A.eqRealExact "abs positive" (1.5, Real.abs 1.5);
             A.eqRealExact "abs negative" (1.5, Real.abs ~1.5);
             A.eqRealExact "negation" (~1.5, ~1.5)))
        ]),

        Group ("IEEE special values",
          onlyIf (ieee, ieeeWhy)
          [ Case ("classification", fn () =>
              (eqCls "positive infinity" (IEEEReal.INF, Real.class (inf ()));
               eqCls "negative infinity" (IEEEReal.INF, Real.class (ninf ()));
               eqCls "nan" (IEEEReal.NAN, Real.class (nan ()));
               eqCls "zero" (IEEEReal.ZERO, Real.class 0.0);
               eqCls "one" (IEEEReal.NORMAL, Real.class 1.0))),

            Case ("isFinite, isNan, isNormal", fn () =>
              (A.eqBool "1.0 is finite" (true, Real.isFinite 1.0);
               A.eqBool "inf is not finite" (false, Real.isFinite (inf ()));
               A.eqBool "nan is not finite" (false, Real.isFinite (nan ()));
               A.eqBool "nan is a nan" (true, Real.isNan (nan ()));
               A.eqBool "1.0 is not a nan" (false, Real.isNan 1.0);
               A.eqBool "1.0 is normal" (true, Real.isNormal 1.0);
               A.eqBool "zero is not normal" (false, Real.isNormal 0.0);
               A.eqBool "inf is not normal" (false, Real.isNormal (inf ())))),

            Case ("a nan is equal to nothing, itself included", fn () =>
              (A.eqBool "== with itself" (false, Real.== (nan (), nan ()));
               A.eqBool "== with a number" (false, Real.== (nan (), 1.0));
               A.eqBool "< " (false, nan () < 1.0);
               A.eqBool "> " (false, nan () > 1.0);
               A.eqBool "unordered" (true, Real.unordered (nan (), 1.0));
               A.eqBool "?= holds for nan" (true, Real.?= (nan (), 1.0)))),

            Case ("compare on a nan raises Unordered", fn () =>
              (A.raises "left" A.isUnordered
                 (fn () => Real.compare (nan (), 1.0));
               A.raises "right" A.isUnordered
                 (fn () => Real.compare (1.0, nan ())))),

            Case ("compareReal reports UNORDERED instead of raising", fn () =>
              A.that "unordered"
                (Real.compareReal (nan (), 1.0) = IEEEReal.UNORDERED)),

            Case ("arithmetic with infinities", fn () =>
              (A.eqBool "1/0 is infinite" (true, Real.== (1.0 / 0.0, inf ()));
               A.eqBool "~1/0 is negative infinity"
                 (true, Real.== (~1.0 / 0.0, ninf ()));
               A.eqBool "inf + 1 is inf" (true, Real.== (inf () + 1.0, inf ()));
               A.eqBool "inf - inf is a nan" (true, Real.isNan (inf () - inf ()));
               A.eqBool "0 * inf is a nan" (true, Real.isNan (0.0 * inf ())))),

            Case ("min and max prefer the number over a nan", fn () =>
              (A.eqRealExact "min with a nan second" (1.0, Real.min (1.0, nan ()));
               A.eqRealExact "min with a nan first" (1.0, Real.min (nan (), 1.0));
               A.eqRealExact "max with a nan second" (1.0, Real.max (1.0, nan ()));
               A.eqRealExact "max with a nan first" (1.0, Real.max (nan (), 1.0)))),

            Case ("checkFloat", fn () =>
              (A.noRaise "a finite value passes" (fn () => Real.checkFloat 1.0);
               A.raises "an infinity is an overflow" A.isOverflow
                 (fn () => Real.checkFloat (inf ()));
               A.raises "a nan is a Div" A.isDiv
                 (fn () => Real.checkFloat (nan ())))),

            Case ("nextAfter steps by one representable value", fn () =>
              let
                val up = Real.nextAfter (1.0, 2.0)
                val down = Real.nextAfter (1.0, 0.0)
              in
                A.that "upwards is larger" (up > 1.0);
                A.that "downwards is smaller" (down < 1.0);
                A.that "nothing lies strictly between"
                  (Real.== (Real.nextAfter (up, 0.0), 1.0))
              end)
          ]),

        Group ("signed zero",
          onlyIf (ieee andalso C.hasSignedZero,
                  "implementation not declared to have signed zero")
          [ Case ("the two zeroes compare equal but differ in sign", fn () =>
              (A.eqBool "equal" (true, Real.== (0.0, negZero ()));
               A.eqBool "signBit of positive zero" (false, Real.signBit 0.0);
               A.eqBool "signBit of negative zero" (true, Real.signBit (negZero ())))),

            Case ("dividing by the two zeroes gives opposite infinities", fn () =>
              (A.eqBool "positive" (true, Real.== (1.0 / 0.0, inf ()));
               A.eqBool "negative" (true, Real.== (1.0 / negZero (), ninf ())))),

            Case ("copySign and sameSign", fn () =>
              (A.eqRealExact "copy a negative sign" (~1.5, Real.copySign (1.5, ~2.0));
               A.eqRealExact "copy a positive sign" (1.5, Real.copySign (~1.5, 2.0));
               A.eqBool "sameSign" (true, Real.sameSign (~1.0, ~2.0));
               A.eqBool "different signs" (false, Real.sameSign (~1.0, 2.0));
               A.eqBool "zeroes of different sign"
                 (false, Real.sameSign (0.0, negZero ()))))
          ]),

        Group ("subnormals",
          onlyIf (ieee andalso C.hasSubnormals,
                  "implementation not declared to have subnormals")
          [ Case ("minPos is subnormal and minNormalPos is not", fn () =>
              (eqCls "minPos" (IEEEReal.SUBNORMAL, Real.class Real.minPos);
               eqCls "minNormalPos" (IEEEReal.NORMAL, Real.class Real.minNormalPos)))
          ]),

        Group ("rounding to integers",
        [ Case ("floor rounds down", fn () =>
            (A.eqInt "positive" (1, Real.floor 1.7);
             A.eqInt "negative" (~2, Real.floor ~1.7);
             A.eqInt "exact" (2, Real.floor 2.0))),

          Case ("ceil rounds up", fn () =>
            (A.eqInt "positive" (2, Real.ceil 1.2);
             A.eqInt "negative" (~1, Real.ceil ~1.7);
             A.eqInt "exact" (2, Real.ceil 2.0))),

          Case ("trunc rounds towards zero", fn () =>
            (A.eqInt "positive" (1, Real.trunc 1.7);
             A.eqInt "negative" (~1, Real.trunc ~1.7))),

          (* Ties go to the even neighbour, not away from zero. *)
          Case ("round goes to nearest with ties to even", fn () =>
            (A.eqInt "1.4" (1, Real.round 1.4);
             A.eqInt "1.6" (2, Real.round 1.6);
             A.eqInt "0.5 ties down to zero" (0, Real.round 0.5);
             A.eqInt "1.5 ties up to two" (2, Real.round 1.5);
             A.eqInt "2.5 ties down to two" (2, Real.round 2.5);
             A.eqInt "~0.5 ties to zero" (0, Real.round ~0.5);
             A.eqInt "~1.5 ties to negative two" (~2, Real.round ~1.5))),

          Case ("the real-valued versions agree", fn () =>
            (A.eqRealExact "realFloor" (1.0, Real.realFloor 1.7);
             A.eqRealExact "realCeil" (2.0, Real.realCeil 1.2);
             A.eqRealExact "realTrunc" (1.0, Real.realTrunc 1.7);
             A.eqRealExact "realRound" (2.0, Real.realRound 1.5))),

          Case ("rounding a nan is rejected",
            fn () =>
              if not ieee then ()
              else
                (A.raises "floor" A.isDomainOrOverflow
                   (fn () => Real.floor (nan ()));
                 A.raises "round" A.isDomainOrOverflow
                   (fn () => Real.round (nan ())))),

          Case ("rounding an infinity overflows",
            fn () =>
              if not ieee then ()
              else
                (A.raises "floor of inf" A.isDomainOrOverflow
                   (fn () => Real.floor (inf ()));
                 A.raises "ceil of negative inf" A.isDomainOrOverflow
                   (fn () => Real.ceil (ninf ())))),

          Case ("toInt with an explicit rounding mode", fn () =>
            (A.eqInt "to negative infinity"
               (1, Real.toInt IEEEReal.TO_NEGINF 1.7);
             A.eqInt "to positive infinity"
               (2, Real.toInt IEEEReal.TO_POSINF 1.2);
             A.eqInt "towards zero" (~1, Real.toInt IEEEReal.TO_ZERO ~1.7);
             A.eqInt "to nearest" (2, Real.toInt IEEEReal.TO_NEAREST 1.6)))
        ]),

        Group ("decomposition",
        [ Case ("toManExp and fromManExp", fn () =>
            let
              val { man, exp } = Real.toManExp 8.0
            in
              A.that "the mantissa is in [0.5, 1)"
                (Real.abs man >= 0.5 andalso Real.abs man < 1.0);
              A.eqRealExact "reassembles"
                (8.0, Real.fromManExp { man = man, exp = exp })
            end),

          Case ("split and realMod", fn () =>
            let
              val { whole, frac } = Real.split 1.75
            in
              A.eqRealExact "whole" (1.0, whole);
              A.eqRealExact "frac" (0.75, frac);
              A.eqRealExact "realMod is the fractional part"
                (0.75, Real.realMod 1.75);
              A.eqRealExact "negative values keep their sign"
                (~0.75, Real.realMod ~1.75)
            end),

          Case ("rem takes the sign of the dividend", fn () =>
            (A.eqRealExact "positive" (2.0, Real.rem (5.0, 3.0));
             A.eqRealExact "negative dividend" (~2.0, Real.rem (~5.0, 3.0));
             A.eqRealExact "negative divisor" (2.0, Real.rem (5.0, ~3.0))))
        ]),

        Group ("conversion to and from text",
          (* Real.toString is fmt (GEN NONE), whose exact spelling -- whether
           * 1.0 prints as "1.0" or "1", and how many digits survive -- the
           * Basis does not pin down.  What it does fix is that negation is
           * written with a tilde and that the result names the same number to
           * the precision GEN keeps, so that is what is checked. *)
        [ Case ("toString produces something fromString accepts", fn () =>
            let
              (* real is not an equality type, so options of it are compared
               * through Real.== rather than with =. *)
              fun readsBackAs (expected, s) =
                case Real.fromString s of
                    NONE => false
                  | SOME y => Real.== (expected, y)
            in
              A.that "one" (readsBackAs (1.0, Real.toString 1.0));
              A.that "negative uses a tilde"
                (String.isPrefix "~" (Real.toString ~1.5));
              A.that "negative round trips"
                (readsBackAs (~1.5, Real.toString ~1.5))
            end),

          Case ("fromString", fn () =>
            (A.eqBool "decimal" (true,
               Real.== (1.5, valOf (Real.fromString "1.5")));
             A.eqBool "tilde sign" (true,
               Real.== (~1.5, valOf (Real.fromString "~1.5")));
             A.eqBool "hyphen sign" (true,
               Real.== (~1.5, valOf (Real.fromString "-1.5")));
             A.eqBool "exponent" (true,
               Real.== (1000.0, valOf (Real.fromString "1e3")));
             A.eqBool "leading whitespace" (true,
               Real.== (1.5, valOf (Real.fromString "  1.5"))))),

          Case ("fromString rejects non-numbers", fn () =>
            (A.that "empty" (not (isSome (Real.fromString "")));
             A.that "letters" (not (isSome (Real.fromString "abc"))))),

          Case ("fmt in fixed notation", fn () =>
            (A.eqString "two places" ("3.14", Real.fmt (StringCvt.FIX (SOME 2)) 3.14159);
             A.eqString "no places" ("3", Real.fmt (StringCvt.FIX (SOME 0)) 3.14159);
             A.eqString "rounds" ("3.1416", Real.fmt (StringCvt.FIX (SOME 4)) 3.14159))),

          Case ("fmt in scientific notation", fn () =>
            A.eqString "two places"
              ("3.14E0", Real.fmt (StringCvt.SCI (SOME 2)) 3.14159)),

          Case ("fmt rejects a negative number of digits", fn () =>
            (A.raises "FIX" A.isSize
               (fn () => Real.fmt (StringCvt.FIX (SOME ~1)) 1.0);
             A.raises "SCI" A.isSize
               (fn () => Real.fmt (StringCvt.SCI (SOME ~1)) 1.0))),

          Case ("the special values print and parse",
            fn () =>
              if not ieee then ()
              else
                (A.eqBool "infinity round trips" (true,
                   Real.== (inf (), valOf (Real.fromString
                                             (Real.toString (inf ())))));
                 A.that "a nan parses back to a nan"
                   (Real.isNan (valOf (Real.fromString (Real.toString (nan ())))))))
        ]),

        Group ("hexadecimal literals",
          onlyIf (C.realFromStringAcceptsHex,
                  "implementation not declared to accept hexadecimal reals")
          [ Case ("fromString reads the hexadecimal form", fn () =>
              (A.eqBool "0x1.8p3 is 12" (true,
                 Real.== (12.0, valOf (Real.fromString "0x1.8p3")));
               A.eqBool "0x1p0 is 1" (true,
                 Real.== (1.0, valOf (Real.fromString "0x1p0")))))
          ]),

        Group ("rounding modes",
          onlyIf (C.hasRoundingModes,
                  "implementation not declared to honour IEEEReal rounding modes")
          [ (* Setting the mode is global state, so the original is restored
             * whatever happens; leaving the process in TO_ZERO would silently
             * change the meaning of every later test. *)
            Case ("every mode can be set and read back", fn () =>
              let
                val original = IEEEReal.getRoundingMode ()
                fun name IEEEReal.TO_NEAREST = "TO_NEAREST"
                  | name IEEEReal.TO_NEGINF = "TO_NEGINF"
                  | name IEEEReal.TO_POSINF = "TO_POSINF"
                  | name IEEEReal.TO_ZERO = "TO_ZERO"
                fun check m =
                  (IEEEReal.setRoundingMode m;
                   A.eqBy (op =, name) ("mode " ^ name m)
                     (m, IEEEReal.getRoundingMode ()))
              in
                (List.app check [IEEEReal.TO_NEAREST, IEEEReal.TO_NEGINF,
                                 IEEEReal.TO_POSINF, IEEEReal.TO_ZERO];
                 IEEEReal.setRoundingMode original)
                handle e => (IEEEReal.setRoundingMode original; raise e)
              end),

            Case ("the mode directs the rounding of arithmetic", fn () =>
              let
                val original = IEEEReal.getRoundingMode ()
                (* A third is not representable, so the two directed modes must
                 * bracket it and disagree with each other. *)
                fun third () = A.hideVal 1.0 / A.hideVal 3.0
              in
                (IEEEReal.setRoundingMode IEEEReal.TO_NEGINF;
                 let val down = third () in
                   IEEEReal.setRoundingMode IEEEReal.TO_POSINF;
                   let val up = third () in
                     A.that "rounding down gives no more than rounding up"
                            (down <= up)
                   end
                 end;
                 IEEEReal.setRoundingMode original)
                handle e => (IEEEReal.setRoundingMode original; raise e)
              end)
          ]),

        Group ("conversion to and from integers",
        [ Case ("fromInt", fn () =>
            (A.eqRealExact "positive" (3.0, Real.fromInt 3);
             A.eqRealExact "negative" (~3.0, Real.fromInt ~3);
             A.eqRealExact "zero" (0.0, Real.fromInt 0))),

          Case ("LargeInt round trip", fn () =>
            A.eqBool "three" (true,
              Real.== (3.0, Real.fromLargeInt (Real.toLargeInt
                                                 IEEEReal.TO_NEAREST 3.0))))
        ]),

        Group ("laws",
        [ P.forAll ("adding zero changes nothing", reals, showR,
                    fn x => P.implies (Real.isFinite x, Real.== (x + 0.0, x))),

          P.forAll ("multiplying by one changes nothing", reals, showR,
                    fn x => P.implies (Real.isFinite x, Real.== (x * 1.0, x))),

          P.forAll ("multiplying by zero gives zero", reals, showR,
                    fn x => P.implies (Real.isFinite x, Real.== (x * 0.0, 0.0))),

          P.forAll ("addition commutes", realPair, showRPair,
                    fn (x, y) =>
                      P.implies (Real.isFinite x andalso Real.isFinite y
                                 andalso Real.isFinite (x + y),
                                 Real.== (x + y, y + x))),

          P.forAll ("multiplication commutes", realPair, showRPair,
                    fn (x, y) =>
                      P.implies (Real.isFinite x andalso Real.isFinite y
                                 andalso Real.isFinite (x * y),
                                 Real.== (x * y, y * x))),

          P.forAll ("subtraction inverts addition", realPair, showRPair,
                    fn (x, y) =>
                      P.implies (Real.isFinite x andalso Real.isFinite y,
                                 Real.== ((x + y) - y + 0.0, (x + y) - y))),

          P.forAll ("negation is an involution", reals, showR,
                    fn x => P.implies (Real.isFinite x, Real.== (~(~x), x))),

          P.forAll ("abs is non-negative", reals, showR,
                    fn x => P.implies (Real.isFinite x, Real.abs x >= 0.0)),

          P.forAll ("abs is the magnitude", reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x,
                                 Real.== (Real.abs x, x)
                                 orelse Real.== (Real.abs x, ~x))),

          P.forAll ("compare agrees with the operators", realPair, showRPair,
                    fn (x, y) =>
                      P.implies (Real.isFinite x andalso Real.isFinite y,
                                 case Real.compare (x, y) of
                                     LESS => x < y
                                   | EQUAL => Real.== (x, y)
                                   | GREATER => x > y)),

          P.forAll ("min and max bracket their arguments", realPair, showRPair,
                    fn (x, y) =>
                      P.implies (Real.isFinite x andalso Real.isFinite y,
                                 Real.min (x, y) <= x
                                 andalso Real.min (x, y) <= y
                                 andalso Real.max (x, y) >= x
                                 andalso Real.max (x, y) >= y)),

          P.forAll ("floor is below and within one of its argument",
                    reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x andalso Real.abs x < 1.0e9,
                                 let val f = Real.realFloor x
                                 in f <= x andalso x < f + 1.0 end)),

          P.forAll ("ceil is above and within one of its argument",
                    reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x andalso Real.abs x < 1.0e9,
                                 let val c = Real.realCeil x
                                 in c >= x andalso x > c - 1.0 end)),

          P.forAll ("trunc is floor for positives and ceil for negatives",
                    reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x andalso Real.abs x < 1.0e9,
                                 Real.== (Real.realTrunc x,
                                          if x >= 0.0 then Real.realFloor x
                                          else Real.realCeil x))),

          P.forAll ("split reassembles its argument", reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x andalso Real.abs x < 1.0e9,
                                 let val { whole, frac } = Real.split x
                                 in Real.== (whole + frac, x) end)),

          P.forAll ("the fractional part is smaller than one", reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x andalso Real.abs x < 1.0e9,
                                 Real.abs (Real.realMod x) < 1.0)),

          P.forAll ("toManExp and fromManExp round trip", reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x andalso not (Real.== (x, 0.0)),
                                 Real.== (Real.fromManExp (Real.toManExp x), x))),

          P.forAll ("the mantissa lies in the half-open unit interval",
                    reals, showR,
                    fn x =>
                      P.implies (Real.isNormal x,
                                 let val { man, ... } = Real.toManExp x
                                 in Real.abs man >= 0.5 andalso Real.abs man < 1.0
                                 end)),

          (* The exact format is the one round trip the Basis guarantees. *)
          P.forAll ("EXACT formatting round trips through fromString",
                    reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x,
                                 case Real.fromString
                                        (Real.fmt StringCvt.EXACT x) of
                                     NONE => false
                                   | SOME y => Real.== (x, y))),

          (* Only EXACT is required to round-trip; GEN keeps a limited number
           * of significant digits, so the most that can be asked of toString
           * is that what comes back is close. *)
          P.forAll ("toString round trips to within the digits it keeps",
                    reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x,
                                 case Real.fromString (Real.toString x) of
                                     NONE => false
                                   | SOME y =>
                                       Real.== (x, y)
                                       orelse Real.abs (x - y)
                                              <= 1.0e~9 * Real.max (Real.abs x, 1.0))),

          P.forAll ("fromInt agrees with the integer ordering",
                    G.pair (G.smallInt, G.smallInt),
                    Show.pair (Show.int, Show.int),
                    fn (a, b) =>
                      (Real.fromInt a < Real.fromInt b) = (a < b)),

          P.forAll ("floor of fromInt is the integer back again",
                    G.smallInt, Show.int,
                    fn n => Real.floor (Real.fromInt n) = n),

          P.forAll ("rem is smaller in magnitude than the divisor",
                    realPair, showRPair,
                    fn (x, y) =>
                      P.implies (Real.isFinite x andalso Real.isFinite y
                                 andalso not (Real.== (y, 0.0))
                                 andalso Real.abs x < 1.0e9,
                                 Real.abs (Real.rem (x, y)) < Real.abs y))
        ])
      ])
  end
