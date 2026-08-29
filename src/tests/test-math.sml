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
                      < tol)
        ])
      ])
  end
