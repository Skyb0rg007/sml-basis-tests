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

    (* Real.toDecimal and Real.fromDecimal are the two members most often
     * absent, and a build may supply them from src/compat to compile at all.
     * Where it has, the tests below would be testing this suite's own code,
     * so they are skipped with that as the reason. *)
    (* A real small enough that rounding it to an int cannot overflow: the
     * int range is narrower than the real range on most implementations. *)
    fun inIntRange x =
      Real.abs x < 1.0e9
      andalso (case (Int.maxInt, Int.minInt) of
                   (SOME hi, SOME lo) =>
                     x < Real.fromInt hi - 1.0 andalso x > Real.fromInt lo + 1.0
                 | _ => true)

    val ownDecimal = not (Compat.isSubstituted "Real.toDecimal")
    val decimalWhy = "Real.toDecimal comes from src/compat on this build"

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

            (* The specification fixes each combination of an infinity with a
             * finite value, and says which combinations produce NaN. *)
            Case ("addition and subtraction with infinities", fn () =>
              (A.that "5 - (~inf) is inf" (Real.== (5.0 - ninf (), inf ()));
               A.that "inf + inf is inf" (Real.== (inf () + inf (), inf ()));
               A.that "~inf + ~inf is ~inf"
                 (Real.== (ninf () + ninf (), ninf ()));
               A.that "inf + ~inf is a nan" (Real.isNan (inf () + ninf ()));
               A.that "inf - inf is a nan" (Real.isNan (inf () - inf ()));
               A.that "~inf - ~inf is a nan" (Real.isNan (ninf () - ninf ()));
               A.that "a finite value plus inf is inf"
                 (Real.== (5.0 + inf (), inf ())))),

            Case ("multiplication with infinities", fn () =>
              (A.that "0 * inf is a nan" (Real.isNan (0.0 * inf ()));
               A.that "inf * 0 is a nan" (Real.isNan (inf () * 0.0));
               A.that "0 * ~inf is a nan" (Real.isNan (0.0 * ninf ()));
               A.that "~5 * ~inf is inf" (Real.== (~5.0 * ninf (), inf ()));
               A.that "5 * ~inf is ~inf" (Real.== (5.0 * ninf (), ninf ()));
               A.that "inf * ~inf is ~inf"
                 (Real.== (inf () * ninf (), ninf ()));
               A.that "inf * inf is inf" (Real.== (inf () * inf (), inf ())))),

            Case ("division with zeros and infinities", fn () =>
              (A.that "0/0 is a nan" (Real.isNan (0.0 / 0.0));
               A.that "inf/inf is a nan" (Real.isNan (inf () / inf ()));
               A.that "~inf/inf is a nan" (Real.isNan (ninf () / inf ()));
               A.that "inf/~inf is a nan" (Real.isNan (inf () / ninf ()));
               A.that "a non-zero finite over zero is an infinity"
                 (Real.== (5.0 / 0.0, inf ()));
               A.that "a negative finite over zero is a negative infinity"
                 (Real.== (~5.0 / 0.0, ninf ()));
               A.that "an infinity over a finite value is an infinity"
                 (Real.== (inf () / 5.0, inf ()));
               A.that "an infinity over a negative finite value flips sign"
                 (Real.== (inf () / ~5.0, ninf ()));
               A.that "a finite value over an infinity is zero"
                 (Real.== (5.0 / inf (), 0.0));
               A.that "and keeps the sign"
                 (Real.signBit (5.0 / ninf ())))),

            (* "If x is an infinity or y is 0, rem returns NaN.  If y is an
             * infinity, rem returns x." *)
            Case ("rem on the special values", fn () =>
              (A.that "an infinite dividend" (Real.isNan (Real.rem (inf (), 3.0)));
               A.that "a zero divisor" (Real.isNan (Real.rem (5.0, 0.0)));
               A.that "a nan dividend" (Real.isNan (Real.rem (nan (), 3.0)));
               A.eqRealExact "an infinite divisor returns the dividend"
                 (5.0, Real.rem (5.0, inf ()));
               A.eqRealExact "with a negative infinity too"
                 (5.0, Real.rem (5.0, ninf ())))),

            (* "abs (+-0.0) = +0.0   abs (+-infinity) = +infinity
             *  abs (+-NaN) = +NaN", and "~ (+-infinity) = -+infinity". *)
            Case ("abs and negation on the special values", fn () =>
              (A.that "abs of an infinity" (Real.== (Real.abs (ninf ()), inf ()));
               A.that "abs of a nan is a nan" (Real.isNan (Real.abs (nan ())));
               A.eqBool "abs clears the sign bit of a nan"
                 (false, Real.signBit (Real.abs (~(nan ()))));
               A.that "negating an infinity" (Real.== (~(inf ()), ninf ()));
               A.that "and back again" (Real.== (~(ninf ()), inf ())))),

            Case ("min and max of two nans is a nan", fn () =>
              (A.that "min" (Real.isNan (Real.min (nan (), nan ())));
               A.that "max" (Real.isNan (Real.max (nan (), nan ()))))),

            (* "returns ~1 if r is negative, 0 if r is zero, or 1 if r is
             * positive.  An infinity returns its sign." *)
            Case ("sign of an infinity is its sign", fn () =>
              (A.eqInt "positive infinity" (1, Real.sign (inf ()));
               A.eqInt "negative infinity" (~1, Real.sign (ninf ())))),

            (* "This returns true if either argument is NaN or if the
             * arguments are bitwise equal, ignoring signs on zeros." *)
            Case ("the IEEE predicates on nans", fn () =>
              (A.eqBool "?= with a nan on the left" (true, Real.?= (nan (), 1.0));
               A.eqBool "?= with a nan on the right" (true, Real.?= (1.0, nan ()));
               A.eqBool "?= with two nans" (true, Real.?= (nan (), nan ()));
               A.eqBool "?= on equal numbers" (true, Real.?= (1.0, 1.0));
               A.eqBool "?= on different numbers" (false, Real.?= (1.0, 2.0));
               A.eqBool "!= with a nan is true" (true, Real.!= (nan (), nan ()));
               A.eqBool "unordered with no nan"
                 (false, Real.unordered (1.0, 2.0)))),

            (* "Note that these operators return false on unordered
             * arguments ... so that the usual reversal of comparison under
             * negation does not hold." *)
            Case ("every ordering operator is false on a nan", fn () =>
              (A.eqBool "<" (false, nan () < 1.0);
               A.eqBool "<=" (false, nan () <= 1.0);
               A.eqBool ">" (false, nan () > 1.0);
               A.eqBool ">=" (false, nan () >= 1.0);
               A.eqBool "a nan against itself" (false, nan () <= nan ());
               A.eqBool "the reversal under negation fails"
                 (true, (nan () < 1.0) <> not (nan () >= 1.0)))),

            (* "If r is +-0, man is +-0 and exp is +0.  If r is +-infinity,
             * man is +-infinity ... If r is NaN, man is NaN." *)
            Case ("toManExp and fromManExp on the special values", fn () =>
              let
                val zero = Real.toManExp 0.0
                val posinf = Real.toManExp (inf ())
                val notNum = Real.toManExp (nan ())
              in
                A.that "zero has a zero mantissa" (Real.== (#man zero, 0.0));
                A.eqInt "and a zero exponent" (0, #exp zero);
                A.that "an infinity has an infinite mantissa"
                  (Real.== (#man posinf, inf ()));
                A.that "a nan has a nan mantissa" (Real.isNan (#man notNum));
                A.that "fromManExp of a zero mantissa is zero"
                  (Real.== (0.0, Real.fromManExp { man = 0.0, exp = 3 }));
                A.that "fromManExp of an infinite mantissa is an infinity"
                  (Real.== (ninf (), Real.fromManExp { man = ninf (), exp = 3 }));
                A.that "fromManExp of a nan mantissa is a nan"
                  (Real.isNan (Real.fromManExp { man = nan (), exp = 3 }))
              end),

            (* "If r is +-infinity, whole is +-infinity and frac is +-0.  If
             * r is NaN, both whole and frac are NaN." *)
            Case ("split on the special values", fn () =>
              let
                val atInf = Real.split (inf ())
                val atNan = Real.split (nan ())
              in
                A.that "an infinity is all whole"
                  (Real.== (#whole atInf, inf ()));
                A.that "with a zero fractional part"
                  (Real.== (#frac atInf, 0.0));
                A.that "a nan has a nan whole part" (Real.isNan (#whole atNan));
                A.that "and a nan fractional part" (Real.isNan (#frac atNan))
              end),

            (* "If r = t then it returns r.  If either argument is NaN, this
             * returns NaN.  If r is +-infinity, it returns +-infinity." *)
            Case ("nextAfter on equal, nan and infinite arguments", fn () =>
              (A.eqRealExact "equal arguments" (1.0, Real.nextAfter (1.0, 1.0));
               A.that "a nan first" (Real.isNan (Real.nextAfter (nan (), 1.0)));
               A.that "a nan second" (Real.isNan (Real.nextAfter (1.0, nan ())));
               A.that "from an infinity"
                 (Real.== (inf (), Real.nextAfter (inf (), 1.0)));
               A.that "from a negative infinity"
                 (Real.== (ninf (), Real.nextAfter (ninf (), 1.0))))),

            (* "These functions ... If r is NaN or an infinity, these
             * functions return r." *)
            Case ("the real-valued roundings pass the special values through",
              fn () =>
                (A.that "realFloor of an infinity"
                   (Real.== (inf (), Real.realFloor (inf ())));
                 A.that "realCeil of a negative infinity"
                   (Real.== (ninf (), Real.realCeil (ninf ())));
                 A.that "realTrunc of an infinity"
                   (Real.== (inf (), Real.realTrunc (inf ())));
                 A.that "realRound of a nan"
                   (Real.isNan (Real.realRound (nan ())));
                 A.that "realFloor of a nan"
                   (Real.isNan (Real.realFloor (nan ()))))),

            (* "In all cases, positive and negative infinities are converted
             * to "inf" and "~inf", respectively, and NaN values are converted
             * to the string "nan"." *)
            Case ("every format prints the special values the same way",
              fn () =>
                let
                  fun check (name, spec) =
                    (A.eqString (name ^ " of an infinity")
                       ("inf", Real.fmt spec (inf ()));
                     A.eqString (name ^ " of a negative infinity")
                       ("~inf", Real.fmt spec (ninf ()));
                     A.eqString (name ^ " of a nan")
                       ("nan", Real.fmt spec (nan ())))
                in
                  List.app check
                    [("FIX", StringCvt.FIX (SOME 2)),
                     ("SCI", StringCvt.SCI (SOME 2)),
                     ("GEN", StringCvt.GEN (SOME 3)),
                     ("EXACT", StringCvt.EXACT)];
                  A.eqString "toString of an infinity"
                    ("inf", Real.toString (inf ()));
                  A.eqString "toString of a nan" ("nan", Real.toString (nan ()))
                end),

            (* "It also accepts the following string representations of
             * non-finite values: [+~-]?(inf | infinity | nan), where the
             * alphabetic characters are case-insensitive." *)
            Case ("fromString reads the non-finite spellings", fn () =>
              let
                fun isInf s =
                  case Real.fromString s of
                      SOME r => Real.== (r, inf ())
                    | NONE => false
                fun isNegInf s =
                  case Real.fromString s of
                      SOME r => Real.== (r, ninf ())
                    | NONE => false
                fun isANan s =
                  case Real.fromString s of
                      SOME r => Real.isNan r
                    | NONE => false
              in
                A.that "inf" (isInf "inf");
                A.that "infinity" (isInf "infinity");
                A.that "INF" (isInf "INF");
                A.that "Infinity" (isInf "Infinity");
                A.that "+inf" (isInf "+inf");
                A.that "~inf" (isNegInf "~inf");
                A.that "-infinity" (isNegInf "-infinity");
                A.that "nan" (isANan "nan");
                A.that "NaN" (isANan "NaN");
                A.that "~nan" (isANan "~nan")
              end),

            (* "Values of too large a magnitude are represented as infinities;
             * values of too small a magnitude are represented as zeros." *)
            Case ("scanning a magnitude that does not fit", fn () =>
              (A.that "too large is an infinity"
                 (case Real.fromString "1e999999" of
                      SOME r => Real.== (r, inf ())
                    | NONE => false);
               A.that "too large and negative is a negative infinity"
                 (case Real.fromString "~1e999999" of
                      SOME r => Real.== (r, ninf ())
                    | NONE => false);
               A.that "too small is a zero"
                 (case Real.fromString "1e~999999" of
                      SOME r => Real.== (r, 0.0)
                    | NONE => false))),

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

          (* "fmt raises Size if spec is an invalid precision, i.e., if spec
           * is SCI (SOME i) with i < 0, FIX (SOME i) with i < 0, or
           * GEN (SOME i) with i < 1." *)
          Case ("fmt rejects a negative number of digits", fn () =>
            (A.raises "FIX" A.isSize
               (fn () => Real.fmt (StringCvt.FIX (SOME ~1)) 1.0);
             A.raises "SCI" A.isSize
               (fn () => Real.fmt (StringCvt.SCI (SOME ~1)) 1.0);
             A.raises "GEN of zero digits" A.isSize
               (fn () => Real.fmt (StringCvt.GEN (SOME 0)) 1.0);
             A.raises "GEN of a negative count" A.isSize
               (fn () => Real.fmt (StringCvt.GEN (SOME ~1)) 1.0))),

          (* "The exception should be raised when fmt spec is evaluated" --
           * that is, by the partial application, before any real is given. *)
          Case ("fmt rejects the specification before it sees a value", fn () =>
            (A.raises "FIX" A.isSize
               (fn () => Real.fmt (StringCvt.FIX (SOME ~1)));
             A.raises "SCI" A.isSize
               (fn () => Real.fmt (StringCvt.SCI (SOME ~1)));
             A.raises "GEN" A.isSize
               (fn () => Real.fmt (StringCvt.GEN (SOME 0))))),

          Case ("scientific notation with no fractional digits", fn () =>
            (A.eqString "no decimal point"
               ("3E0", Real.fmt (StringCvt.SCI (SOME 0)) 3.14159);
             A.eqString "the exponent carries the magnitude"
               ("3E2", Real.fmt (StringCvt.SCI (SOME 0)) 314.159))),

          (* "[+~-]?([0-9]+.[0-9]+? | .[0-9]+)(e | E)[+~-]?[0-9]+?" *)
          Case ("fromString accepts every shape in the grammar", fn () =>
            let
              fun reads (expected, s) =
                case Real.fromString s of
                    NONE => false
                  | SOME y => Real.== (expected, y)
            in
              A.that "a leading plus" (reads (1.5, "+1.5"));
              A.that "a leading hyphen" (reads (~1.5, "-1.5"));
              A.that "a leading tilde" (reads (~1.5, "~1.5"));
              A.that "no fractional digits" (reads (1.0, "1."));
              A.that "no integral digits" (reads (0.5, ".5"));
              A.that "an upper-case exponent" (reads (1500.0, "1.5E3"));
              A.that "a lower-case exponent" (reads (1500.0, "1.5e3"));
              A.that "a signed exponent" (reads (0.0015, "1.5e~3"));
              A.that "a hyphen in the exponent" (reads (0.0015, "1.5e-3"));
              A.that "a plus in the exponent" (reads (1500.0, "1.5e+3"));
              A.that "an integer with no point" (reads (42.0, "42"))
            end),

          Case ("scan stops where the grammar stops", fn () =>
            let
              fun restAfter s =
                case Real.scan Substring.getc (Substring.full s) of
                    NONE => NONE
                  | SOME (r, rest) => SOME (Substring.string rest)
            in
              A.eqStringOption "an exponent with no digits keeps the e"
                (SOME "e", restAfter "1.5e");
              A.eqStringOption "trailing letters" (SOME "abc", restAfter "1.5abc");
              A.eqStringOption "a second point" (SOME ".5", restAfter "1.5.5")
            end),

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
            (* "The IEEE standard requires TO_NEAREST as the default rounding
             * mode." *)
            Case ("the mode starts out as TO_NEAREST", fn () =>
              A.that "TO_NEAREST"
                (IEEEReal.getRoundingMode () = IEEEReal.TO_NEAREST)),

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

        Group ("fused arithmetic and sign",
        [ (* *+ and *- are the fused multiply-add operations: a*b+c and
           * a*b-c, computed as a single operation. *)
          Case ("multiply-add", fn () =>
            (A.eqRealExact "2*3+4" (10.0, Real.*+ (2.0, 3.0, 4.0));
             A.eqRealExact "with a negative addend"
               (2.0, Real.*+ (2.0, 3.0, ~4.0));
             A.eqRealExact "adding zero" (6.0, Real.*+ (2.0, 3.0, 0.0)))),

          Case ("multiply-subtract", fn () =>
            (A.eqRealExact "2*3-4" (2.0, Real.*- (2.0, 3.0, 4.0));
             A.eqRealExact "subtracting zero" (6.0, Real.*- (2.0, 3.0, 0.0)))),

          Case ("sign classifies", fn () =>
            (A.eqInt "positive" (1, Real.sign 2.5);
             A.eqInt "negative" (~1, Real.sign ~2.5);
             A.eqInt "zero" (0, Real.sign 0.0))),

          Case ("sign of a negative zero is still zero",
            fn () =>
              if not (ieee andalso C.hasSignedZero) then ()
              else A.eqInt "negative zero" (0, Real.sign (negZero ()))),

          (* Unlike signBit, sign has no answer for a NaN. *)
          Case ("sign of a nan is a Domain error",
            fn () =>
              if not ieee then ()
              else A.raises "sign nan" A.isDomain (fn () => Real.sign (nan ())))
        ]),

        Group ("scanning",
        [ Case ("scan reads a real and leaves the rest", fn () =>
            case Real.scan Substring.getc (Substring.full "1.5 tail") of
                NONE => A.fail "scan returned NONE"
              | SOME (r, rest) =>
                  (A.eqRealExact "value" (1.5, r);
                   A.eqString "remainder" (" tail", Substring.string rest))),

          Case ("scan skips leading whitespace", fn () =>
            case Real.scan Substring.getc (Substring.full "   2.5") of
                NONE => A.fail "scan returned NONE"
              | SOME (r, _) => A.eqRealExact "value" (2.5, r)),

          Case ("scan reads an exponent", fn () =>
            case Real.scan Substring.getc (Substring.full "1e3") of
                NONE => A.fail "scan returned NONE"
              | SOME (r, _) => A.eqRealExact "value" (1000.0, r)),

          Case ("scan rejects what is not a real", fn () =>
            A.that "letters"
              (not (isSome (Real.scan Substring.getc (Substring.full "abc"))))),

          Case ("fmt in general notation", fn () =>
            (A.eqString "three significant digits"
               ("3.14", Real.fmt (StringCvt.GEN (SOME 3)) 3.14159);
             A.raises "a negative digit count" A.isSize
               (fn () => Real.fmt (StringCvt.GEN (SOME ~1)) 1.0)))
        ]),

        Group ("decimal approximations",
        onlyIf (ownDecimal, decimalWhy)
        [ (* toDecimal reports the value as 0.d1d2...dn times 10^exp. *)
          Case ("toDecimal decomposes a value", fn () =>
            let
              val d = Real.toDecimal 1.5
            in
              eqCls "class" (IEEEReal.NORMAL, #class d);
              A.eqBool "sign" (false, #sign d);
              A.eqIntList "digits" ([1, 5], #digits d);
              A.eqInt "exponent" (1, #exp d)
            end),

          Case ("a negative value sets the sign and keeps the digits", fn () =>
            let
              val d = Real.toDecimal ~12.25
            in
              A.eqBool "sign" (true, #sign d);
              A.eqIntList "digits" ([1, 2, 2, 5], #digits d);
              A.eqInt "exponent" (2, #exp d)
            end),

          Case ("zero has no digits", fn () =>
            let
              val d = Real.toDecimal 0.0
            in
              eqCls "class" (IEEEReal.ZERO, #class d);
              A.eqIntList "digits" ([], #digits d)
            end),

          Case ("trailing zeroes are not kept", fn () =>
            let
              val d = Real.toDecimal 100.0
            in
              A.eqIntList "one digit" ([1], #digits d);
              A.eqInt "and the exponent carries the magnitude" (3, #exp d)
            end),

          Case ("fromDecimal inverts toDecimal", fn () =>
            (case Real.fromDecimal (Real.toDecimal 1.5) of
                 NONE => A.fail "fromDecimal returned NONE"
               | SOME r => A.eqRealExact "value" (1.5, r);
             case Real.fromDecimal (Real.toDecimal ~12.25) of
                 NONE => A.fail "fromDecimal returned NONE"
               | SOME r => A.eqRealExact "negative value" (~12.25, r))),

          Case ("IEEEReal.toString writes the decimal form", fn () =>
            (A.eqString "one and a half"
               ("0.15E1", IEEEReal.toString (Real.toDecimal 1.5));
             A.eqString "a negative value"
               ("~0.1225E2", IEEEReal.toString (Real.toDecimal ~12.25)))),

          (* "For toDecimal, when the r is not normal or subnormal, then the
           * exp field is set to 0 and the digits field is the empty list.  In
           * all cases, the sign and class field capture the sign and class of
           * r." *)
          Case ("toDecimal of a value that is neither normal nor subnormal",
            fn () =>
              if not ieee then ()
              else
                let
                  val atInf = Real.toDecimal (inf ())
                  val atNan = Real.toDecimal (nan ())
                  val atZero = Real.toDecimal 0.0
                in
                  eqCls "an infinity" (IEEEReal.INF, #class atInf);
                  A.eqInt "with a zero exponent" (0, #exp atInf);
                  A.eqIntList "and no digits" ([], #digits atInf);
                  A.eqBool "and a positive sign" (false, #sign atInf);
                  eqCls "a nan" (IEEEReal.NAN, #class atNan);
                  A.eqInt "with a zero exponent" (0, #exp atNan);
                  A.eqIntList "and no digits" ([], #digits atNan);
                  A.eqInt "a zero has a zero exponent" (0, #exp atZero);
                  A.eqBool "a negative infinity keeps its sign"
                    (true, #sign (Real.toDecimal (ninf ())))
                end),

          (* "if class is ZERO or INF, the resulting real is the appropriate
           * signed zero or infinity.  If class is NAN, a signed NaN is
           * generated." *)
          Case ("fromDecimal on the non-finite classes", fn () =>
            if not ieee then ()
            else
              let
                fun build (cls, sign) =
                  Real.fromDecimal { class = cls, sign = sign,
                                     digits = [], exp = 0 }
              in
                A.that "an infinity"
                  (case build (IEEEReal.INF, false) of
                       SOME r => Real.== (r, inf ())
                     | NONE => false);
                A.that "a negative infinity"
                  (case build (IEEEReal.INF, true) of
                       SOME r => Real.== (r, ninf ())
                     | NONE => false);
                A.that "a nan"
                  (case build (IEEEReal.NAN, false) of
                       SOME r => Real.isNan r
                     | NONE => false);
                A.that "a zero"
                  (case build (IEEEReal.ZERO, false) of
                       SOME r => Real.== (r, 0.0)
                     | NONE => false)
              end),

          (* "Note that the conversion itself should ignore the class field
           * ... For example, if digits is empty or a list of all 0's, the
           * result should be a signed zero." *)
          Case ("fromDecimal reads the digits, not the class", fn () =>
            (A.that "digits that spell a number"
               (case Real.fromDecimal { class = IEEEReal.NORMAL, sign = false,
                                        digits = [1, 5], exp = 1 } of
                    SOME r => Real.== (r, 1.5)
                  | NONE => false);
             A.that "a negative sign"
               (case Real.fromDecimal { class = IEEEReal.NORMAL, sign = true,
                                        digits = [1, 5], exp = 1 } of
                    SOME r => Real.== (r, ~1.5)
                  | NONE => false);
             A.that "no digits is a zero"
               (case Real.fromDecimal { class = IEEEReal.NORMAL, sign = false,
                                        digits = [], exp = 3 } of
                    SOME r => Real.== (r, 0.0)
                  | NONE => false);
             A.that "digits that are all zero is a zero"
               (case Real.fromDecimal { class = IEEEReal.NORMAL, sign = false,
                                        digits = [0, 0], exp = 3 } of
                    SOME r => Real.== (r, 0.0)
                  | NONE => false))),

          (* "If the argument to fromDecimal does not have a valid format,
           * i.e., if the digits field contains integers outside the range
           * [0,9], it returns NONE." *)
          Case ("fromDecimal rejects a digit outside the range", fn () =>
            (A.that "ten"
               (not (isSome (Real.fromDecimal
                               { class = IEEEReal.NORMAL, sign = false,
                                 digits = [1, 10], exp = 1 })));
             A.that "a negative digit"
               (not (isSome (Real.fromDecimal
                               { class = IEEEReal.NORMAL, sign = false,
                                 digits = [~1], exp = 1 })))))
        ]
        @
        [ Case ("IEEEReal.fromString reads it back", fn () =>
            case IEEEReal.fromString "0.15E1" of
                NONE => A.fail "fromString returned NONE"
              | SOME d =>
                  (A.eqBool "sign" (false, #sign d);
                   A.eqIntList "digits" ([1, 5], #digits d);
                   A.eqInt "exponent" (1, #exp d))),

          Case ("IEEEReal.scan leaves the rest of the stream", fn () =>
            case IEEEReal.scan Substring.getc (Substring.full "0.15E1 tail") of
                NONE => A.fail "scan returned NONE"
              | SOME (d, rest) =>
                  (A.eqIntList "digits" ([1, 5], #digits d);
                   A.eqString "remainder" (" tail", Substring.string rest))),

          Case ("IEEEReal.fromString rejects what is not a number", fn () =>
            A.that "letters" (not (isSome (IEEEReal.fromString "abc")))),

          (* "Assuming digits = [d(1), ..., d(n)] and ignoring the sign and
           * exp fields, toString generates the following strings depending on
           * the class field ... If the sign field is true, a #"~" is
           * prepended.  If the exp field is non-zero and the class is NORMAL
           * or SUBNORMAL, the string "E"^(Integer.toString exp) is
           * appended." *)
          Case ("IEEEReal.toString follows the table", fn () =>
            let
              fun d (cls, sign, digits, exp) =
                IEEEReal.toString { class = cls, sign = sign,
                                    digits = digits, exp = exp }
            in
              A.eqString "a zero" ("0.0", d (IEEEReal.ZERO, false, [], 0));
              A.eqString "a negative zero"
                ("~0.0", d (IEEEReal.ZERO, true, [], 0));
              A.eqString "an infinity" ("inf", d (IEEEReal.INF, false, [], 0));
              A.eqString "a negative infinity"
                ("~inf", d (IEEEReal.INF, true, [], 0));
              A.eqString "a nan" ("nan", d (IEEEReal.NAN, false, [], 0));
              A.eqString "a normal value with no exponent"
                ("0.15", d (IEEEReal.NORMAL, false, [1, 5], 0));
              A.eqString "a normal value with an exponent"
                ("0.15E3", d (IEEEReal.NORMAL, false, [1, 5], 3));
              A.eqString "a negative normal value"
                ("~0.15E3", d (IEEEReal.NORMAL, true, [1, 5], 3));
              A.eqString "a negative exponent"
                ("0.15E~3", d (IEEEReal.NORMAL, false, [1, 5], ~3));
              A.eqString "a subnormal value prints like a normal one"
                ("0.15E3", d (IEEEReal.SUBNORMAL, false, [1, 5], 3));
              A.eqString "the exponent of an infinity is ignored"
                ("inf", d (IEEEReal.INF, false, [], 3))
            end),

          (* "The optional sign determines the value of the sign field ...
           * If il is non-empty, then class is set to NORMAL, digits is set to
           * il@fl with any trailing zeros removed and exp is set to the
           * length of il plus the value of the scanned exponent." *)
          Case ("IEEEReal.fromString decomposes as the specification says",
            fn () =>
              let
                fun parts s =
                  case IEEEReal.fromString s of
                      NONE => NONE
                    | SOME d => SOME (#sign d, #digits d, #exp d)
                val show =
                  Show.option (Show.triple (Show.bool, Show.intList, Show.int))
                val eq = A.eqBy (op =, show)
              in
                eq "an integer part only"
                  (SOME (false, [1, 2, 3], 3), parts "123");
                eq "leading zeros are stripped from the integer part"
                  (SOME (false, [1, 2, 3], 3), parts "000123");
                eq "trailing zeros are stripped from the fraction"
                  (SOME (false, [1, 2, 3], 3), parts "123.000");
                eq "an integer and a fraction"
                  (SOME (false, [1, 2, 3, 4, 5], 3), parts "123.45");
                eq "a negative sign" (SOME (true, [1, 5], 1), parts "~1.5");
                eq "a hyphen sign" (SOME (true, [1, 5], 1), parts "-1.5");
                eq "a plus sign" (SOME (false, [1, 5], 1), parts "+1.5");
                eq "an exponent adds to the length of the integer part"
                  (SOME (false, [1, 5], 4), parts "1.5e3");
                eq "no integer part" (SOME (false, [5], 0), parts "0.5");
                eq "leading zeros in the fraction lower the exponent"
                  (SOME (false, [5], ~2), parts "0.005");
                eq "and combine with the exponent"
                  (SOME (false, [5], 1), parts "0.005e3");
                eq "a zero has no digits" (SOME (false, [], 0), parts "0.0");
                eq "and neither does a signed zero"
                  (SOME (true, [], 0), parts "~0.000")
              end),

          Case ("IEEEReal.fromString reads the non-finite spellings", fn () =>
            let
              fun parts s =
                case IEEEReal.fromString s of
                    NONE => NONE
                  | SOME d => SOME (#class d, #sign d, #digits d, #exp d)
              fun clsName IEEEReal.NAN = "NAN"
                | clsName IEEEReal.INF = "INF"
                | clsName IEEEReal.ZERO = "ZERO"
                | clsName IEEEReal.NORMAL = "NORMAL"
                | clsName IEEEReal.SUBNORMAL = "SUBNORMAL"
              val show =
                Show.option
                  (fn (c, s, ds, e) =>
                     "(" ^ clsName c ^ "," ^ Show.bool s ^ ","
                     ^ Show.intList ds ^ "," ^ Show.int e ^ ")")
              val eq = A.eqBy (op =, show)
            in
              eq "inf" (SOME (IEEEReal.INF, false, [], 0), parts "inf");
              eq "infinity" (SOME (IEEEReal.INF, false, [], 0), parts "infinity");
              eq "INF, case-insensitively"
                (SOME (IEEEReal.INF, false, [], 0), parts "INF");
              eq "a negative infinity"
                (SOME (IEEEReal.INF, true, [], 0), parts "~inf");
              eq "nan" (SOME (IEEEReal.NAN, false, [], 0), parts "nan");
              eq "NaN, case-insensitively"
                (SOME (IEEEReal.NAN, false, [], 0), parts "NaN");
              eq "a signed nan" (SOME (IEEEReal.NAN, true, [], 0), parts "-nan")
            end),

          (* "The fromString function is equivalent to StringCvt.scanString
           * scan." *)
          Case ("IEEEReal.fromString is scanString scan", fn () =>
            let
              fun norm NONE = NONE
                | norm (SOME (d : IEEEReal.decimal_approx)) =
                    SOME (#sign d, #digits d, #exp d)
              fun sameOn s =
                norm (IEEEReal.fromString s)
                = norm (StringCvt.scanString IEEEReal.scan s)
            in
              List.app (fn s => A.that ("agree on " ^ s) (sameOn s))
                ["1.5", "  1.5", "abc", "", "0.005e3", "inf", "~2"]
            end),

          Case ("IEEEReal.scan skips leading whitespace", fn () =>
            case IEEEReal.scan Substring.getc (Substring.full "   1.5") of
                NONE => A.fail "scan returned NONE"
              | SOME (d, _) => A.eqIntList "digits" ([1, 5], #digits d))
        ]
        @ onlyIf (ownDecimal, decimalWhy)
        [ (* "The composition toString o REAL.toDecimal is equivalent to
           * REAL.fmt StringCvt.EXACT." *)
          P.forAll ("toString of toDecimal is the EXACT format", reals, showR,
                    fn x =>
                      IEEEReal.toString (Real.toDecimal x)
                      = Real.fmt StringCvt.EXACT x)
        ]),

        Group ("conversion to and from integers",
        [ Case ("fromInt", fn () =>
            (A.eqRealExact "positive" (3.0, Real.fromInt 3);
             A.eqRealExact "negative" (~3.0, Real.fromInt ~3);
             A.eqRealExact "zero" (0.0, Real.fromInt 0))),

          Case ("LargeInt round trip", fn () =>
            A.eqBool "three" (true,
              Real.== (3.0, Real.fromLargeInt (Real.toLargeInt
                                                 IEEEReal.TO_NEAREST 3.0)))),

          (* "The top-level function real is an alias for Real.fromInt." *)
          Case ("the top-level real is Real.fromInt", fn () =>
            (A.eqRealExact "a positive value" (Real.fromInt 3, real 3);
             A.eqRealExact "a negative value" (Real.fromInt ~7, real ~7))),

          (* "These functions convert the argument x to an integral type using
           * the specified rounding mode.  They raise Overflow if the result
           * is not representable ... They raise Domain if the input real is
           * NaN." *)
          Case ("toLargeInt rounds in the mode it is given", fn () =>
            (A.eqLargeInt "to negative infinity"
               (LargeInt.fromInt 1, Real.toLargeInt IEEEReal.TO_NEGINF 1.7);
             A.eqLargeInt "to positive infinity"
               (LargeInt.fromInt 2, Real.toLargeInt IEEEReal.TO_POSINF 1.2);
             A.eqLargeInt "towards zero"
               (LargeInt.fromInt ~1, Real.toLargeInt IEEEReal.TO_ZERO ~1.7);
             A.eqLargeInt "to nearest"
               (LargeInt.fromInt 2, Real.toLargeInt IEEEReal.TO_NEAREST 1.6);
             A.eqLargeInt "ties go to even"
               (LargeInt.fromInt 2, Real.toLargeInt IEEEReal.TO_NEAREST 2.5))),

          Case ("toInt and toLargeInt reject the special values", fn () =>
            if not ieee then ()
            else
              (A.raises "toInt of an infinity" A.isDomainOrOverflow
                 (fn () => Real.toInt IEEEReal.TO_NEAREST (inf ()));
               A.raises "toInt of a nan" A.isDomainOrOverflow
                 (fn () => Real.toInt IEEEReal.TO_NEAREST (nan ()));
               A.raises "toLargeInt of an infinity" A.isDomainOrOverflow
                 (fn () => Real.toLargeInt IEEEReal.TO_NEAREST (inf ()));
               A.raises "toLargeInt of a nan" A.isDomainOrOverflow
                 (fn () => Real.toLargeInt IEEEReal.TO_NEAREST (nan ())))),

          Case ("toInt reports a value the int cannot hold", fn () =>
            case Int.maxInt of
                NONE => ()
              | SOME big =>
                  let
                    (* Real.fromInt maxInt is exactly representable only up to
                     * rounding, so go well past it. *)
                    val tooBig = Real.fromInt big * 4.0
                  in
                    if not (Real.isFinite tooBig) then ()
                    else A.raises "past maxInt" A.isOverflow
                           (fn () => Real.toInt IEEEReal.TO_ZERO tooBig)
                  end),

          (* "These convert between values of type real and type
           * LargeReal.real." *)
          Case ("conversion through LargeReal round trips", fn () =>
            (A.that "a whole number"
               (Real.== (3.5, Real.fromLarge IEEEReal.TO_NEAREST
                                             (Real.toLarge 3.5)));
             A.that "a negative value"
               (Real.== (~0.25, Real.fromLarge IEEEReal.TO_NEAREST
                                               (Real.toLarge ~0.25)))))
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

          P.forAll ("multiply-add agrees with multiplying then adding",
                    G.triple (reals, reals, reals),
                    Show.triple (showR, showR, showR),
                    fn (a, b, c) =>
                      P.implies (Real.isFinite a andalso Real.isFinite b
                                 andalso Real.isFinite c
                                 andalso Real.isFinite (a * b + c),
                                 (* The fused form may be more accurate, so
                                  * equality is not required -- only that the
                                  * two agree to within a rounding step. *)
                                 let
                                   val fused = Real.*+ (a, b, c)
                                   val plain = a * b + c
                                 in
                                   Real.== (fused, plain)
                                   orelse Real.abs (fused - plain)
                                          <= 1.0e~9 * Real.max (Real.abs plain, 1.0)
                                 end)),

          P.forAll ("multiply-subtract is multiply-add with a negated addend",
                    G.triple (reals, reals, reals),
                    Show.triple (showR, showR, showR),
                    fn (a, b, c) =>
                      P.implies (Real.isFinite a andalso Real.isFinite b
                                 andalso Real.isFinite c
                                 andalso Real.isFinite (a * b - c),
                                 Real.== (Real.*- (a, b, c), Real.*+ (a, b, ~c)))),

          P.forAll ("sign agrees with comparison against zero", reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x,
                                 case Real.sign x of
                                     0 => Real.== (x, 0.0)
                                   | 1 => x > 0.0
                                   | ~1 => x < 0.0
                                   | _ => false)),

          P.forAll ("scan inverts the exact format", reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x,
                                 case Real.scan Substring.getc
                                        (Substring.full
                                           (Real.fmt StringCvt.EXACT x)) of
                                     NONE => false
                                   | SOME (y, _) => Real.== (x, y))),

          (* "The value returned by toString is equivalent to
           *  (fmt (StringCvt.GEN NONE) r)." *)
          P.forAll ("toString is fmt (GEN NONE)", reals, showR,
                    fn x => Real.toString x = Real.fmt (StringCvt.GEN NONE) x),

          (* "The second version ... is equivalent to StringCvt.scanString
           * scan." *)
          P.forAll ("fromString is scanString scan",
                    G.oneOf [ G.map Real.toString reals,
                              G.printableString ],
                    Show.string,
                    fn s =>
                      let
                        val a = Real.fromString s
                        val b = StringCvt.scanString Real.scan s
                      in
                        case (a, b) of
                            (NONE, NONE) => true
                          | (SOME x, SOME y) => Real.== (x, y) orelse
                                                (Real.isNan x andalso Real.isNan y)
                          | _ => false
                      end),

          (* "returns the remainder x - n*y, where n = trunc (x / y).  The
           * result has the same sign as x and has absolute value less than
           * the absolute value of y."  The reference expression x - n*y is
           * itself computed in floating point, so it is only compared to
           * within the rounding error of the larger operand; the quotient is
           * kept small enough that n is exactly representable. *)
          P.forAll ("rem is the remainder after truncating division",
                    realPair, showRPair,
                    fn (x, y) =>
                      P.implies
                        (Real.isFinite x andalso Real.isFinite y
                         andalso not (Real.== (y, 0.0))
                         andalso Real.abs (x / y) < 1.0e6,
                         let
                           val n = Real.realTrunc (x / y)
                           val r = Real.rem (x, y)
                           val slack =
                             1.0e~9 * Real.max (Real.abs x, Real.abs y)
                         in
                           Real.abs (r - (x - n * y)) <= slack
                           andalso Real.abs r < Real.abs y
                           andalso (Real.== (r, 0.0)
                                    orelse Real.signBit r = Real.signBit x)
                         end)),

          (* "returns a*b + c and a*b - c, respectively." *)
          P.forAll ("multiply-subtract is the product less the third argument",
                    G.triple (reals, reals, reals),
                    Show.triple (showR, showR, showR),
                    fn (a, b, c) =>
                      P.implies (Real.isFinite (a * b - c),
                                 Real.abs (Real.*- (a, b, c) - (a * b - c))
                                 <= 1.0e~9 * Real.max (1.0, Real.abs (a * b)))),

          (* "returns true if and only if signBit r1 equals signBit r2." *)
          P.forAll ("sameSign is equality of sign bits", realPair, showRPair,
                    fn (x, y) =>
                      Real.sameSign (x, y) = (Real.signBit x = Real.signBit y)),

          (* "returns x with the sign of y, even if y is NaN." *)
          P.forAll ("copySign takes the magnitude of one and the sign of the other",
                    realPair, showRPair,
                    fn (x, y) =>
                      let val z = Real.copySign (x, y)
                      in
                        Real.signBit z = Real.signBit y
                        andalso Real.== (Real.abs z, Real.abs x)
                      end),

          (* "The second function != is equivalent to not o op ==." *)
          P.forAll ("!= is the negation of ==", realPair, showRPair,
                    fn (x, y) => Real.!= (x, y) = not (Real.== (x, y))),

          P.forAll ("?= holds exactly when the arguments are equal or unordered",
                    realPair, showRPair,
                    fn (x, y) =>
                      Real.?= (x, y)
                      = (Real.unordered (x, y) orelse Real.== (x, y))),

          P.forAll ("unordered means one of the arguments is a nan",
                    realPair, showRPair,
                    fn (x, y) =>
                      Real.unordered (x, y)
                      = (Real.isNan x orelse Real.isNan y)),

          (* "returns true if x is normal, i.e., neither zero, subnormal,
           * infinite nor NaN", and class agrees with each predicate. *)
          P.forAll ("the predicates agree with the classification", reals, showR,
                    fn x =>
                      let val c = Real.class x
                      in
                        Real.isFinite x
                        = (c <> IEEEReal.INF andalso c <> IEEEReal.NAN)
                        andalso Real.isNan x = (c = IEEEReal.NAN)
                        andalso Real.isNormal x = (c = IEEEReal.NORMAL)
                      end),

          (* "we have the relation r = man * radix(exp) where
           *  1.0 <= man * radix < radix." *)
          P.forAll ("the mantissa is scaled into one radix step", reals, showR,
                    fn x =>
                      P.implies
                        (Real.isFinite x andalso not (Real.== (x, 0.0)),
                         let
                           val { man, exp } = Real.toManExp x
                           val radix = Real.fromInt Real.radix
                           val m = Real.abs man * radix
                         in
                           m >= 1.0 andalso m < radix
                           andalso Real.== (x, Real.fromManExp { man = man,
                                                                 exp = exp })
                         end)),

          (* "whole is integral, |frac| < 1.0, whole and frac have the same
           * sign as r, and r = whole + frac", and "realMod is equivalent to
           * #frac o split". *)
          P.forAll ("split reports an integral part and a matching fraction",
                    reals, showR,
                    fn x =>
                      P.implies
                        (Real.isFinite x,
                         let
                           val { whole, frac } = Real.split x
                         in
                           Real.== (Real.realTrunc whole, whole)
                           andalso Real.abs frac < 1.0
                           andalso Real.== (x, whole + frac)
                           andalso Real.== (Real.realMod x, frac)
                           andalso (Real.== (frac, 0.0)
                                    orelse Real.signBit frac = Real.signBit x)
                           andalso (Real.== (whole, 0.0)
                                    orelse Real.signBit whole = Real.signBit x)
                         end)),

          (* "These are respectively equivalent to:
           *  toInt IEEEReal.TO_NEGINF r, toInt IEEEReal.TO_POSINF r,
           *  toInt IEEEReal.TO_ZERO r, toInt IEEEReal.TO_NEAREST r." *)
          P.forAll ("the integer roundings are toInt in the four modes",
                    reals, showR,
                    fn x =>
                      (* Deferred: the conclusion itself overflows outside the
                       * int range, and the int range is narrower than the
                       * real range. *)
                      P.impliesBy
                        (Real.isFinite x andalso inIntRange x,
                         fn () =>
                         Real.floor x = Real.toInt IEEEReal.TO_NEGINF x
                         andalso Real.ceil x = Real.toInt IEEEReal.TO_POSINF x
                         andalso Real.trunc x = Real.toInt IEEEReal.TO_ZERO x
                         andalso Real.round x = Real.toInt IEEEReal.TO_NEAREST x)),

          P.forAll ("the real-valued roundings agree with the integer ones",
                    reals, showR,
                    fn x =>
                      P.impliesBy
                        (Real.isFinite x andalso inIntRange x,
                         fn () =>
                         Real.== (Real.realFloor x,
                                  Real.fromInt (Real.floor x))
                         andalso Real.== (Real.realCeil x,
                                          Real.fromInt (Real.ceil x))
                         andalso Real.== (Real.realTrunc x,
                                          Real.fromInt (Real.trunc x))
                         andalso Real.== (Real.realRound x,
                                          Real.fromInt (Real.round x)))),

          P.forAll ("toLargeInt agrees with toInt where both fit",
                    reals, showR,
                    fn x =>
                      P.impliesBy
                        (Real.isFinite x andalso inIntRange x,
                         fn () =>
                         Real.toLargeInt IEEEReal.TO_NEAREST x
                         = Int.toLarge (Real.toInt IEEEReal.TO_NEAREST x))),

          P.forAll ("LargeReal conversion round trips", reals, showR,
                    fn x =>
                      Real.== (x, Real.fromLarge IEEEReal.TO_NEAREST
                                                 (Real.toLarge x))
                      orelse Real.isNan x),

          (* The Discussion: "~x is ... identical to x but with its sign bit
           * flipped." *)
          P.forAll ("negation flips the sign bit", reals, showR,
                    fn x => Real.signBit (~x) = not (Real.signBit x)),

          P.forAll ("min and max choose one of their arguments",
                    realPair, showRPair,
                    fn (x, y) =>
                      let
                        val lo = Real.min (x, y)
                        val hi = Real.max (x, y)
                      in
                        (Real.== (lo, x) orelse Real.== (lo, y))
                        andalso (Real.== (hi, x) orelse Real.== (hi, y))
                      end),

          (* "checkFloat raises Overflow if x is an infinity, and raises Div
           * if x is NaN.  Otherwise, it returns its argument." *)
          P.forAll ("checkFloat is the identity on finite values", reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x,
                                 Real.== (x, Real.checkFloat x))),

          (* fmt's three notations have the shapes the specification writes
           * out as regular expressions. *)
          P.forAll ("scientific notation has one digit before the point",
                    reals, showR,
                    fn x =>
                      P.implies
                        (Real.isFinite x,
                         let
                           val s = Real.fmt (StringCvt.SCI (SOME 3)) x
                           val body = if String.isPrefix "~" s
                                      then String.extract (s, 1, NONE) else s
                           val (mant, ex) =
                             Substring.splitl (fn c => c <> #"E")
                                              (Substring.full body)
                           val m = Substring.string mant
                         in
                           String.size m = 5            (* d.ddd *)
                           andalso Char.isDigit (String.sub (m, 0))
                           andalso String.sub (m, 1) = #"."
                           andalso Substring.size ex > 1
                           andalso Substring.sub (ex, 0) = #"E"
                         end)),

          P.forAll ("fixed notation has at least one digit before the point",
                    reals, showR,
                    fn x =>
                      P.implies
                        (Real.isFinite x,
                         let
                           val s = Real.fmt (StringCvt.FIX (SOME 2)) x
                           val body = if String.isPrefix "~" s
                                      then String.extract (s, 1, NONE) else s
                           val (whole, frac) =
                             Substring.splitl (fn c => c <> #".")
                                              (Substring.full body)
                         in
                           Substring.size whole >= 1
                           andalso List.all Char.isDigit
                                            (Substring.explode whole)
                           andalso Substring.size frac = 3   (* ".dd" *)
                         end)),

          P.forAll ("a zero digit count leaves out the decimal point",
                    reals, showR,
                    fn x =>
                      P.implies
                        (Real.isFinite x,
                         not (Char.contains (Real.fmt (StringCvt.FIX (SOME 0)) x)
                                            #".")
                         andalso not (Char.contains
                                        (Substring.string
                                           (Substring.takel (fn c => c <> #"E")
                                              (Substring.full
                                                 (Real.fmt (StringCvt.SCI (SOME 0)) x))))
                                        #".")))
        ]
        @ onlyIf (ownDecimal, decimalWhy)
        [ P.forAll ("fromDecimal inverts toDecimal", reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x,
                                 case Real.fromDecimal (Real.toDecimal x) of
                                     NONE => false
                                   | SOME y => Real.== (x, y))),

          P.forAll ("the decimal digits are digits", reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x,
                                 List.all (fn d => d >= 0 andalso d <= 9)
                                          (#digits (Real.toDecimal x)))),

          P.forAll ("IEEEReal round trips the decimal form", reals, showR,
                    fn x =>
                      P.implies (Real.isFinite x,
                                 case IEEEReal.fromString
                                        (IEEEReal.toString (Real.toDecimal x)) of
                                     NONE => false
                                   | SOME d =>
                                       (case Real.fromDecimal d of
                                            NONE => false
                                          | SOME y => Real.== (x, y))))
        ]
        @
        [ P.forAll ("fromInt agrees with the integer ordering",
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
