(* Tests for the Math structure.
 *
 * Floating point transcendental functions are not required to be correctly
 * rounded, so every numeric check here is a tolerance check.  The tolerance
 * is derived from Real.precision rather than hard-coded, so the same source
 * is neither vacuous on a high-precision system nor spuriously failing on a
 * low-precision one.
 *)

functor MathTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    (* One unit in the last place, derived from the implementation's own
     * precision, scaled by the slack the configuration allows. *)
    val ulp =
      let
        fun half (x, 0) = x
          | half (x, n) = half (x / 2.0, n - 1)
      in
        half (1.0, Real.precision - 1)
      end

    val tol = ulp * Real.fromInt C.mathToleranceUlps

    (* Identities that combine several function results accumulate error, so
     * they are given a few multiples of the basic tolerance. *)
    val loose = tol * 4.0

    val near = A.eqRealRel tol
    val showR = Show.real

    (* Arguments kept in a range where the functions are well conditioned. *)
    val moderate = G.map (fn u => (u - 0.5) * 20.0) G.unitReal
    val positive = G.map (fn u => 0.001 + u * 100.0) G.unitReal
    val unitRange = G.map (fn u => u * 2.0 - 1.0) G.unitReal

    val ieee = C.hasIEEEReals
    fun nan () = 0.0 / 0.0
    fun inf () = Real.posInf
    fun ninf () = Real.negInf
    fun negZero () = ~0.0

    (* The specification's exceptional-case tables distinguish +0 from ~0.
     * Where the implementation does not have signed zeros, only the value is
     * checked. *)
    val signedZero = C.hasSignedZero

    fun isNan x = Real.isNan x
    fun isPosInf x = Real.== (x, inf ())
    fun isNegInf x = Real.== (x, ninf ())
    fun isZeroSigned neg x =
      Real.== (x, 0.0)
      andalso (not signedZero orelse Real.signBit x = neg)
    val isPosZero = isZeroSigned false
    val isNegZero = isZeroSigned true

    (* A tolerant equality for the table entries that name a multiple of pi. *)
    fun isNear y x = Real.abs (x - y) < 1.0e~9 * Real.max (1.0, Real.abs y)

    val suite = Group ("Math",
      [ Group ("constants",
        [ Case ("pi", fn () => near "pi" (3.14159265358979, Math.pi)),
          Case ("e", fn () => near "e" (2.71828182845905, Math.e)),
          Case ("the constants are consistent with the functions", fn () =>
            (near "ln e is one" (1.0, Math.ln Math.e);
             near "cos pi is minus one" (~1.0, Math.cos Math.pi);
             near "sin pi is zero" (0.0, Math.sin Math.pi)))
        ]),

        Group ("powers and roots",
        [ Case ("sqrt", fn () =>
            (near "of four" (2.0, Math.sqrt 4.0);
             near "of two" (1.4142135623730951, Math.sqrt 2.0);
             near "of zero" (0.0, Math.sqrt 0.0);
             near "of one" (1.0, Math.sqrt 1.0))),

          Case ("sqrt of a negative number is a nan",
            fn () =>
              if not ieee then ()
              else A.that "nan" (Real.isNan (Math.sqrt ~1.0))),

          Case ("exp and ln", fn () =>
            (near "exp 0" (1.0, Math.exp 0.0);
             near "exp 1" (Math.e, Math.exp 1.0);
             near "ln 1" (0.0, Math.ln 1.0);
             near "ln e" (1.0, Math.ln Math.e))),

          Case ("ln at and below zero",
            fn () =>
              if not ieee then ()
              else
                (A.that "ln 0 is negative infinity"
                   (Real.== (Math.ln 0.0, Real.negInf));
                 A.that "ln of a negative number is a nan"
                   (Real.isNan (Math.ln ~1.0)))),

          Case ("log10", fn () =>
            (near "of one" (0.0, Math.log10 1.0);
             near "of ten" (1.0, Math.log10 10.0);
             near "of a thousand" (3.0, Math.log10 1000.0))),

          Case ("pow", fn () =>
            (near "two cubed" (8.0, Math.pow (2.0, 3.0));
             near "anything to the zero" (1.0, Math.pow (5.0, 0.0));
             near "a square root" (2.0, Math.pow (4.0, 0.5));
             near "a negative exponent" (0.25, Math.pow (2.0, ~2.0))))
        ]),

        Group ("trigonometry",
        [ Case ("sin, cos and tan at familiar points", fn () =>
            (near "sin 0" (0.0, Math.sin 0.0);
             near "cos 0" (1.0, Math.cos 0.0);
             near "tan 0" (0.0, Math.tan 0.0);
             near "sin of a quarter turn" (1.0, Math.sin (Math.pi / 2.0));
             near "cos of a quarter turn" (0.0, Math.cos (Math.pi / 2.0)))),

          Case ("the inverse functions", fn () =>
            (near "asin 0" (0.0, Math.asin 0.0);
             near "asin 1" (Math.pi / 2.0, Math.asin 1.0);
             near "acos 1" (0.0, Math.acos 1.0);
             near "acos 0" (Math.pi / 2.0, Math.acos 0.0);
             near "atan 0" (0.0, Math.atan 0.0);
             near "atan 1" (Math.pi / 4.0, Math.atan 1.0))),

          Case ("asin and acos outside their domain",
            fn () =>
              if not ieee then ()
              else
                (A.that "asin 2 is a nan" (Real.isNan (Math.asin 2.0));
                 A.that "acos 2 is a nan" (Real.isNan (Math.acos 2.0)))),

          Case ("atan2 covers all four quadrants", fn () =>
            (near "first" (Math.pi / 4.0, Math.atan2 (1.0, 1.0));
             near "second" (3.0 * Math.pi / 4.0, Math.atan2 (1.0, ~1.0));
             near "third" (~3.0 * Math.pi / 4.0, Math.atan2 (~1.0, ~1.0));
             near "fourth" (~(Math.pi / 4.0), Math.atan2 (~1.0, 1.0));
             near "on the positive x axis" (0.0, Math.atan2 (0.0, 1.0));
             near "on the positive y axis"
               (Math.pi / 2.0, Math.atan2 (1.0, 0.0)))),

          Case ("the hyperbolic functions", fn () =>
            (near "sinh 0" (0.0, Math.sinh 0.0);
             near "cosh 0" (1.0, Math.cosh 0.0);
             near "tanh 0" (0.0, Math.tanh 0.0);
             near "sinh 1" (1.1752011936438014, Math.sinh 1.0);
             near "cosh 1" (1.5430806348152437, Math.cosh 1.0);
             near "tanh 1" (0.7615941559557649, Math.tanh 1.0)))
        ]),

        (* The specification tabulates the value of each function at the
         * infinities, the zeros and the NaN; those tables are what the
         * following three groups check. *)
        Group ("the exceptional cases of the elementary functions",
          onlyIf (ieee, "implementation not declared IEEE")
          [ Case ("sqrt", fn () =>
              (A.that "sqrt of a negative zero keeps the sign"
                 (isNegZero (Math.sqrt (negZero ())));
               A.that "sqrt of a positive zero" (isPosZero (Math.sqrt 0.0));
               A.that "sqrt of a negative number is a nan"
                 (isNan (Math.sqrt ~1.0));
               A.that "sqrt of an infinity is an infinity"
                 (isPosInf (Math.sqrt (inf ()))))),

            (* "If x is an infinity, these functions return NaN." *)
            Case ("sin, cos and tan at an infinity", fn () =>
              (A.that "sin" (isNan (Math.sin (inf ())));
               A.that "cos" (isNan (Math.cos (inf ())));
               A.that "tan" (isNan (Math.tan (inf ())));
               A.that "sin of a negative infinity" (isNan (Math.sin (ninf ()))))),

            (* "If the magnitude of x exceeds 1.0, they return NaN." *)
            Case ("asin and acos outside the unit interval", fn () =>
              (A.that "asin above" (isNan (Math.asin 1.5));
               A.that "asin below" (isNan (Math.asin ~1.5));
               A.that "acos above" (isNan (Math.acos 1.5));
               A.that "acos below" (isNan (Math.acos ~1.5));
               A.that "asin of an infinity" (isNan (Math.asin (inf ()))))),

            (* "If x is +infinity, it returns pi/2; if x is -infinity, it
             * returns -pi/2." *)
            Case ("atan at the infinities", fn () =>
              (A.that "positive" (isNear (Math.pi / 2.0) (Math.atan (inf ())));
               A.that "negative"
                 (isNear (~(Math.pi / 2.0)) (Math.atan (ninf ()))))),

            (* "If x is +infinity, it returns +infinity; if x is -infinity, it
             * returns 0." *)
            Case ("exp at the infinities", fn () =>
              (A.that "positive" (isPosInf (Math.exp (inf ())));
               A.that "negative" (Real.== (0.0, Math.exp (ninf ()))))),

            (* "If x < 0, they return NaN; if x = 0, they return -infinity; if
             * x is infinity, they return infinity." *)
            Case ("ln and log10 at and outside their domain", fn () =>
              (A.that "ln of zero" (isNegInf (Math.ln 0.0));
               A.that "log10 of zero" (isNegInf (Math.log10 0.0));
               A.that "ln of a negative number" (isNan (Math.ln ~1.0));
               A.that "log10 of a negative number" (isNan (Math.log10 ~1.0));
               A.that "ln of an infinity" (isPosInf (Math.ln (inf ())));
               A.that "log10 of an infinity" (isPosInf (Math.log10 (inf ()))))),

            (* The table of properties for the hyperbolic functions. *)
            Case ("the hyperbolic functions at zero and the infinities",
              fn () =>
                (A.that "sinh of a positive zero" (isPosZero (Math.sinh 0.0));
                 A.that "sinh of a negative zero"
                   (isNegZero (Math.sinh (negZero ())));
                 A.that "sinh of an infinity" (isPosInf (Math.sinh (inf ())));
                 A.that "sinh of a negative infinity"
                   (isNegInf (Math.sinh (ninf ())));
                 A.that "cosh of a zero" (Real.== (1.0, Math.cosh 0.0));
                 A.that "cosh of a negative zero"
                   (Real.== (1.0, Math.cosh (negZero ())));
                 A.that "cosh of an infinity" (isPosInf (Math.cosh (inf ())));
                 (* The table reads "cosh +-infinity = +-infinity", while the
                  * definition given in the same paragraph, (e^x + e^-x)/2,
                  * gives +infinity for both.  The two readings disagree only
                  * here, so both answers are accepted. *)
                 A.that "cosh of a negative infinity"
                   (isPosInf (Math.cosh (ninf ()))
                    orelse isNegInf (Math.cosh (ninf ())));
                 A.that "tanh of a positive zero" (isPosZero (Math.tanh 0.0));
                 A.that "tanh of a negative zero"
                   (isNegZero (Math.tanh (negZero ())));
                 A.that "tanh of an infinity" (Real.== (1.0, Math.tanh (inf ())));
                 A.that "tanh of a negative infinity"
                   (Real.== (~1.0, Math.tanh (ninf ())))))
          ]),

        (* "Rules for exceptional cases are specified in the following
         * table." -- every row of it. *)
        Group ("the exceptional cases of atan2",
          onlyIf (ieee, "implementation not declared IEEE")
          [ Case ("a zero numerator", fn () =>
              (A.that "with a positive denominator"
                 (isPosZero (Math.atan2 (0.0, 1.0)));
               A.that "with a positive zero denominator"
                 (isPosZero (Math.atan2 (0.0, 0.0)));
               A.that "with a negative denominator"
                 (isNear Math.pi (Math.atan2 (0.0, ~1.0))))),

            Case ("a zero numerator of either sign", fn () =>
              if not signedZero then ()
              else
                (A.that "a negative zero over a positive number"
                   (isNegZero (Math.atan2 (negZero (), 1.0)));
                 A.that "a negative zero over a positive zero"
                   (isNegZero (Math.atan2 (negZero (), 0.0)));
                 A.that "a positive zero over a negative zero"
                   (isNear Math.pi (Math.atan2 (0.0, negZero ())));
                 A.that "a negative zero over a negative zero"
                   (isNear (~Math.pi) (Math.atan2 (negZero (), negZero ())));
                 A.that "a negative zero over a negative number"
                   (isNear (~Math.pi) (Math.atan2 (negZero (), ~1.0))))),

            Case ("a zero denominator", fn () =>
              (A.that "a positive numerator"
                 (isNear (Math.pi / 2.0) (Math.atan2 (1.0, 0.0)));
               A.that "a negative numerator"
                 (isNear (~(Math.pi / 2.0)) (Math.atan2 (~1.0, 0.0)));
               if not signedZero then ()
               else
                 (A.that "a positive numerator over a negative zero"
                    (isNear (Math.pi / 2.0) (Math.atan2 (1.0, negZero ())));
                  A.that "a negative numerator over a negative zero"
                    (isNear (~(Math.pi / 2.0))
                            (Math.atan2 (~1.0, negZero ())))))),

            Case ("an infinite denominator", fn () =>
              (A.that "a positive finite over a positive infinity"
                 (isPosZero (Math.atan2 (1.0, inf ())));
               A.that "a positive finite over a negative infinity"
                 (isNear Math.pi (Math.atan2 (1.0, ninf ())));
               A.that "a negative finite over a negative infinity"
                 (isNear (~Math.pi) (Math.atan2 (~1.0, ninf ()))))),

            Case ("an infinite numerator", fn () =>
              (A.that "over a finite value"
                 (isNear (Math.pi / 2.0) (Math.atan2 (inf (), 1.0)));
               A.that "negative, over a finite value"
                 (isNear (~(Math.pi / 2.0)) (Math.atan2 (ninf (), 1.0)));
               A.that "over a positive infinity"
                 (isNear (Math.pi / 4.0) (Math.atan2 (inf (), inf ())));
               A.that "negative, over a positive infinity"
                 (isNear (~(Math.pi / 4.0)) (Math.atan2 (ninf (), inf ())));
               A.that "over a negative infinity"
                 (isNear (3.0 * Math.pi / 4.0) (Math.atan2 (inf (), ninf ())));
               A.that "negative, over a negative infinity"
                 (isNear (~3.0 * Math.pi / 4.0)
                         (Math.atan2 (ninf (), ninf ())))))
          ]),

        Group ("the exceptional cases of pow",
          onlyIf (ieee, "implementation not declared IEEE")
          [ (* "x, including NaN | 0 | 1" *)
            Case ("any base to the zero is one", fn () =>
              (A.that "a number" (Real.== (1.0, Math.pow (2.5, 0.0)));
               A.that "a nan" (Real.== (1.0, Math.pow (nan (), 0.0)));
               A.that "an infinity" (Real.== (1.0, Math.pow (inf (), 0.0)));
               A.that "a zero" (Real.== (1.0, Math.pow (0.0, 0.0))))),

            Case ("an infinite exponent", fn () =>
              (A.that "a base above one, positive exponent"
                 (isPosInf (Math.pow (2.0, inf ())));
               A.that "a base below one, positive exponent"
                 (isPosZero (Math.pow (0.5, inf ())));
               A.that "a base above one, negative exponent"
                 (isPosZero (Math.pow (2.0, ninf ())));
               A.that "a base below one, negative exponent"
                 (isPosInf (Math.pow (0.5, ninf ())));
               A.that "a magnitude above one is what counts"
                 (isPosInf (Math.pow (~2.0, inf ()))))),

            (* "+-1 | +-infinity | NaN" *)
            Case ("one to an infinite power is a nan", fn () =>
              (A.that "one" (isNan (Math.pow (1.0, inf ())));
               A.that "minus one" (isNan (Math.pow (~1.0, inf ())));
               A.that "one to a negative infinity"
                 (isNan (Math.pow (1.0, ninf ()))))),

            Case ("an infinite base", fn () =>
              (A.that "positive, positive exponent"
                 (isPosInf (Math.pow (inf (), 2.0)));
               A.that "positive, negative exponent"
                 (isPosZero (Math.pow (inf (), ~2.0)));
               A.that "negative, odd positive exponent"
                 (isNegInf (Math.pow (ninf (), 3.0)));
               A.that "negative, even positive exponent"
                 (isPosInf (Math.pow (ninf (), 2.0)));
               A.that "negative, non-integral positive exponent"
                 (isPosInf (Math.pow (ninf (), 2.5)));
               A.that "negative, odd negative exponent"
                 (isNegZero (Math.pow (ninf (), ~3.0)));
               A.that "negative, even negative exponent"
                 (isPosZero (Math.pow (ninf (), ~2.0))))),

            Case ("a nan argument", fn () =>
              (A.that "a nan base" (isNan (Math.pow (nan (), 2.0)));
               A.that "a nan exponent" (isNan (Math.pow (2.0, nan ())));
               A.that "both" (isNan (Math.pow (nan (), nan ()))))),

            (* "finite x < 0 | finite non-integer y | NaN" *)
            Case ("a negative base with a non-integral exponent is a nan",
              fn () =>
                (A.that "a half power" (isNan (Math.pow (~2.0, 0.5)));
                 A.that "a negative non-integral power"
                   (isNan (Math.pow (~2.0, ~1.5)));
                 A.that "an integral power is fine"
                   (Real.== (~8.0, Math.pow (~2.0, 3.0))))),

            Case ("a zero base", fn () =>
              (A.that "odd negative exponent"
                 (isPosInf (Math.pow (0.0, ~3.0)));
               A.that "even negative exponent"
                 (isPosInf (Math.pow (0.0, ~2.0)));
               A.that "non-integral negative exponent"
                 (isPosInf (Math.pow (0.0, ~2.5)));
               A.that "odd positive exponent" (isPosZero (Math.pow (0.0, 3.0)));
               A.that "even positive exponent"
                 (isPosZero (Math.pow (0.0, 2.0))))),

            Case ("a negative zero base", fn () =>
              if not signedZero then ()
              else
                (A.that "odd negative exponent"
                   (isNegInf (Math.pow (negZero (), ~3.0)));
                 A.that "even negative exponent"
                   (isPosInf (Math.pow (negZero (), ~2.0)));
                 A.that "odd positive exponent"
                   (isNegZero (Math.pow (negZero (), 3.0)));
                 A.that "even positive exponent"
                   (isPosZero (Math.pow (negZero (), 2.0))))
          )]),

        Group ("laws",
        [ P.forAll ("the Pythagorean identity", moderate, showR,
                    fn x =>
                      Real.abs (Math.sin x * Math.sin x
                                + Math.cos x * Math.cos x - 1.0) < tol),

          P.forAll ("tan is sin over cos", moderate, showR,
                    fn x =>
                      let val c = Math.cos x
                      in
                        P.implies (Real.abs c > 0.01,
                                   Real.abs (Math.tan x - Math.sin x / c)
                                   < tol * Real.max (1.0, Real.abs (Math.tan x)))
                      end),

          P.forAll ("sin is odd and cos is even", moderate, showR,
                    fn x =>
                      Real.abs (Math.sin (~x) + Math.sin x) < tol
                      andalso Real.abs (Math.cos (~x) - Math.cos x) < tol),

          P.forAll ("sin and cos stay within the unit interval",
                    moderate, showR,
                    fn x =>
                      Real.abs (Math.sin x) <= 1.0
                      andalso Real.abs (Math.cos x) <= 1.0),

          P.forAll ("exp and ln are inverse", positive, showR,
                    fn x =>
                      Real.abs (Math.exp (Math.ln x) - x)
                      < tol * Real.max (1.0, Real.abs x)),

          P.forAll ("ln turns products into sums",
                    G.pair (positive, positive), Show.pair (showR, showR),
                    fn (x, y) =>
                      Real.abs (Math.ln (x * y) - (Math.ln x + Math.ln y))
                      < tol * Real.max (1.0, Real.abs (Math.ln (x * y)))),

          P.forAll ("sqrt squared is the argument", positive, showR,
                    fn x =>
                      let val r = Math.sqrt x
                      in Real.abs (r * r - x) < tol * Real.max (1.0, x) end),

          P.forAll ("sqrt of a square is the magnitude", moderate, showR,
                    fn x =>
                      Real.abs (Math.sqrt (x * x) - Real.abs x)
                      < tol * Real.max (1.0, Real.abs x)),

          P.forAll ("pow with exponent two is squaring", moderate, showR,
                    fn x =>
                      Real.abs (Math.pow (x, 2.0) - x * x)
                      < tol * Real.max (1.0, x * x)),

          P.forAll ("pow adds exponents",
                    G.pair (positive, G.map (fn u => u * 3.0) G.unitReal),
                    Show.pair (showR, showR),
                    fn (x, k) =>
                      Real.abs (Math.pow (x, k) * Math.pow (x, k)
                                - Math.pow (x, k + k))
                      < loose * Real.max (1.0, Math.pow (x, k + k))),

          P.forAll ("log10 is ln scaled", positive, showR,
                    fn x =>
                      Real.abs (Math.log10 x - Math.ln x / Math.ln 10.0)
                      < tol * Real.max (1.0, Real.abs (Math.log10 x))),

          P.forAll ("asin inverts sin on its principal range",
                    unitRange, showR,
                    fn x =>
                      Real.abs (Math.sin (Math.asin x) - x) < tol),

          P.forAll ("acos inverts cos on its principal range",
                    unitRange, showR,
                    fn x =>
                      Real.abs (Math.cos (Math.acos x) - x) < tol),

          P.forAll ("atan inverts tan on its principal range",
                    moderate, showR,
                    fn x =>
                      Real.abs (Math.atan (Math.tan x)) <= Math.pi / 2.0 + tol),

          P.forAll ("atan2 with a positive second argument is atan of the ratio",
                    G.pair (moderate, positive), Show.pair (showR, showR),
                    fn (y, x) =>
                      Real.abs (Math.atan2 (y, x) - Math.atan (y / x))
                      < tol),

          P.forAll ("the hyperbolic identity", G.map (fn u => u * 4.0 - 2.0) G.unitReal,
                    showR,
                    fn x =>
                      Real.abs (Math.cosh x * Math.cosh x
                                - Math.sinh x * Math.sinh x - 1.0)
                      < loose),

          P.forAll ("tanh is sinh over cosh",
                    G.map (fn u => u * 4.0 - 2.0) G.unitReal, showR,
                    fn x =>
                      Real.abs (Math.tanh x - Math.sinh x / Math.cosh x)
                      < tol),

          (* "that is, the values (e(x) - e(-x)) / 2, (e(x) + e(-x)) / 2, and
           * (sinh x)/(cosh x)." *)
          P.forAll ("the hyperbolic functions are what their definitions say",
                    G.map (fn u => u * 4.0 - 2.0) G.unitReal, showR,
                    fn x =>
                      Real.abs (Math.sinh x
                                - (Math.exp x - Math.exp (~x)) / 2.0)
                      < loose
                      andalso Real.abs (Math.cosh x
                                        - (Math.exp x + Math.exp (~x)) / 2.0)
                              < loose),

          (* "Its result is guaranteed to be in the closed interval
           * [-pi/2,pi/2]" for asin, "[0,pi]" for acos, and the open interval
           * "(-pi/2,pi/2)" for atan. *)
          P.forAll ("the inverse functions stay in their principal ranges",
                    unitRange, showR,
                    fn x =>
                      let
                        val a = Math.asin x
                        val b = Math.acos x
                      in
                        a >= ~(Math.pi / 2.0) - tol
                        andalso a <= Math.pi / 2.0 + tol
                        andalso b >= 0.0 - tol andalso b <= Math.pi + tol
                      end),

          P.forAll ("atan stays inside a half turn", G.anyReal, showR,
                    fn x =>
                      P.implies (Real.isFinite x,
                                 Math.atan x > ~(Math.pi / 2.0)
                                 andalso Math.atan x < Math.pi / 2.0)),

          (* "returns the arc tangent of (y/x) in the closed interval
           * [-pi,pi] ... It holds that sign (cos (atan2 (y,x))) = sign(x) and
           * sign (sin (atan2 (y,x))) = sign(y)." *)
          P.forAll ("atan2 lands in a full turn and keeps both signs",
                    G.pair (moderate, moderate), Show.pair (showR, showR),
                    fn (y, x) =>
                      let val a = Math.atan2 (y, x)
                      in
                        a >= ~Math.pi - tol andalso a <= Math.pi + tol
                        andalso P.implies (Real.abs x > 0.01
                                           andalso Real.abs y > 0.01,
                                           Real.sign (Math.cos a) = Real.sign x
                                           andalso Real.sign (Math.sin a)
                                                   = Real.sign y)
                      end),

          (* "When x = 0, this corresponds to an angle of 90 degrees, and the
           * result is (real (sign y)) * pi/2.0." *)
          P.forAll ("atan2 with a zero denominator is a quarter turn",
                    moderate, showR,
                    fn y =>
                      P.implies (Real.abs y > 0.01,
                                 Real.abs (Math.atan2 (y, 0.0)
                                           - real (Real.sign y) * Math.pi / 2.0)
                                 < tol)),

          P.forAll ("pow with an integral exponent is repeated multiplication",
                    G.pair (positive, G.int (0, 5)),
                    Show.pair (showR, Show.int),
                    fn (x, k) =>
                      let
                        fun power (_, 0) = 1.0
                          | power (b, n) = b * power (b, n - 1)
                        val expected = power (x, k)
                      in
                        Real.abs (Math.pow (x, real k) - expected)
                        < loose * Real.max (1.0, Real.abs expected)
                      end)
        ])
      ])
  end
