(* Tests for the Int structure.
 *
 * Int.precision, Int.minInt and Int.maxInt are read from the implementation
 * rather than configured: they are discoverable from inside the language, so
 * asking for them in a configuration file would only create an opportunity to
 * disagree with reality.  What *is* configured is whether overflow is trapped
 * at all (C.intOverflowRaises), because a wrapping implementation cannot be
 * detected without provoking the very behaviour under test.
 *)

functor IntTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val fixed = Option.isSome Int.precision
    val checksOverflow = fixed andalso C.intOverflowRaises

    (* Only used inside tests already guarded by `fixed`. *)
    fun maxI () = valOf Int.maxInt
    fun minI () = valOf Int.minInt

    val nonZeroSmall = G.filter (fn n => n <> 0) G.smallInt

    (* Deliberately small: the laws below combine the operands, and combining
     * two arbitrary in-range integers can overflow for reasons that have
     * nothing to do with the law being tested.  Overflow at the boundary is
     * checked separately and exactly, in the unit tests. *)
    val smallPair = G.pair (G.smallInt, G.smallInt)
    val smallTriple = G.triple (G.smallInt, G.smallInt, G.smallInt)
    val divisorPair = G.pair (G.smallInt, nonZeroSmall)
    val showPair = Show.pair (Show.int, Show.int)
    val showTriple = Show.triple (Show.int, Show.int, Show.int)

    val scanDec = StringCvt.scanString (Int.scan StringCvt.DEC)
    val scanHex = StringCvt.scanString (Int.scan StringCvt.HEX)
    val scanOct = StringCvt.scanString (Int.scan StringCvt.OCT)
    val scanBin = StringCvt.scanString (Int.scan StringCvt.BIN)

    val suite = Group ("Int",
      [ Group ("range",
        [ Case ("precision, minInt and maxInt agree about being bounded",
            fn () =>
              A.eqBool "all three defined together"
                (Option.isSome Int.precision,
                 Option.isSome Int.maxInt andalso Option.isSome Int.minInt)),

          Case ("the bounds straddle zero", fn () =>
            if not fixed then ()
            else
              (A.that "maxInt is positive" (maxI () > 0);
               A.that "minInt is negative" (minI () < 0))),

          (* Two's complement gives ~1, a sign-magnitude representation would
           * give 0; the Basis permits either, so accept both and reject
           * anything else. *)
          Case ("maxInt and minInt are symmetric to within one", fn () =>
            if not fixed then ()
            else
              let val s = maxI () + minI ()
              in A.that ("maxInt + minInt = " ^ Int.toString s
                         ^ ", expected 0 or ~1")
                        (s = 0 orelse s = ~1)
              end),

          (* "If precision is SOME(n), then we have minInt = -2^(n-1) and
           * maxInt = 2^(n-1) - 1."  Built by doubling so that no intermediate
           * leaves the range being described. *)
          Case ("precision fixes minInt and maxInt exactly", fn () =>
            if not fixed then ()
            else
              let
                val n = valOf Int.precision
                fun ones (0, acc) = acc
                  | ones (k, acc) = ones (k - 1, 2 * acc + 1)
                val expectedMax = ones (n - 2, 1)   (* 2^(n-1) - 1 *)
              in
                A.eqInt "maxInt = 2^(precision-1) - 1" (expectedMax, maxI ());
                A.eqInt "minInt = ~(2^(precision-1))"
                  (~expectedMax - 1, minI ())
              end),

          Case ("int has at least 31 bits of precision", fn () =>
            if not fixed then ()
            else A.that "maxInt >= 2^30 - 1" (maxI () >= 1073741823))
        ]),

        Group ("comparison and sign",
        [ Case ("compare", fn () =>
            (A.eqOrder "less" (LESS, Int.compare (1, 2));
             A.eqOrder "equal" (EQUAL, Int.compare (2, 2));
             A.eqOrder "greater" (GREATER, Int.compare (3, 2));
             A.eqOrder "across zero" (LESS, Int.compare (~1, 1)))),

          Case ("min and max", fn () =>
            (A.eqInt "min" (1, Int.min (1, 2));
             A.eqInt "max" (2, Int.max (1, 2));
             A.eqInt "min with negatives" (~2, Int.min (~2, ~1));
             A.eqInt "max with negatives" (~1, Int.max (~2, ~1)))),

          Case ("abs", fn () =>
            (A.eqInt "positive" (3, Int.abs 3);
             A.eqInt "negative" (3, Int.abs ~3);
             A.eqInt "zero" (0, Int.abs 0))),

          Case ("sign", fn () =>
            (A.eqInt "positive" (1, Int.sign 5);
             A.eqInt "negative" (~1, Int.sign ~5);
             A.eqInt "zero" (0, Int.sign 0))),

          Case ("sign of minInt does not overflow", fn () =>
            if not fixed then ()
            else A.eqInt "sign minInt" (~1, Int.sign (minI ()))),

          Case ("sameSign", fn () =>
            (A.eqBool "both positive" (true, Int.sameSign (1, 2));
             A.eqBool "both negative" (true, Int.sameSign (~1, ~2));
             A.eqBool "mixed" (false, Int.sameSign (~1, 2));
             A.eqBool "zero with zero" (true, Int.sameSign (0, 0));
             A.eqBool "zero with positive" (false, Int.sameSign (0, 1))))
        ]),

        Group ("division",
        [ (* div and mod round towards negative infinity; quot and rem round
           * towards zero.  They differ exactly when the operands have opposite
           * signs and the division is inexact, so all four sign combinations
           * are spelled out. *)
          Case ("div rounds towards negative infinity", fn () =>
            (A.eqInt "7 div 2" (3, 7 div 2);
             A.eqInt "~7 div 2" (~4, ~7 div 2);
             A.eqInt "7 div ~2" (~4, 7 div ~2);
             A.eqInt "~7 div ~2" (3, ~7 div ~2);
             A.eqInt "exact division is unaffected" (~4, ~8 div 2))),

          Case ("mod takes the sign of the divisor", fn () =>
            (A.eqInt "7 mod 2" (1, 7 mod 2);
             A.eqInt "~7 mod 2" (1, ~7 mod 2);
             A.eqInt "7 mod ~2" (~1, 7 mod ~2);
             A.eqInt "~7 mod ~2" (~1, ~7 mod ~2);
             A.eqInt "exact division gives zero" (0, ~8 mod 2))),

          Case ("quot rounds towards zero", fn () =>
            (A.eqInt "7 quot 2" (3, Int.quot (7, 2));
             A.eqInt "~7 quot 2" (~3, Int.quot (~7, 2));
             A.eqInt "7 quot ~2" (~3, Int.quot (7, ~2));
             A.eqInt "~7 quot ~2" (3, Int.quot (~7, ~2)))),

          Case ("rem takes the sign of the dividend", fn () =>
            (A.eqInt "7 rem 2" (1, Int.rem (7, 2));
             A.eqInt "~7 rem 2" (~1, Int.rem (~7, 2));
             A.eqInt "7 rem ~2" (1, Int.rem (7, ~2));
             A.eqInt "~7 rem ~2" (~1, Int.rem (~7, ~2)))),

          Case ("division by zero", fn () =>
            (A.raises "div" A.isDiv (fn () => 1 div 0);
             A.raises "mod" A.isDiv (fn () => 1 mod 0);
             A.raises "quot" A.isDiv (fn () => Int.quot (A.hide 1, A.hide 0));
             A.raises "rem" A.isDiv (fn () => Int.rem (A.hide 1, A.hide 0));
             A.raises "zero divided by zero" A.isDiv (fn () => 0 div 0)))
        ]),

        Group ("overflow",
          onlyIf (checksOverflow,
                  if fixed then "implementation declared not to trap overflow"
                  else "int is arbitrary precision")
          [ Case ("addition past maxInt", fn () =>
              A.raises "maxInt + 1" A.isOverflow (fn () => maxI () + 1)),

            Case ("subtraction past minInt", fn () =>
              A.raises "minInt - 1" A.isOverflow (fn () => minI () - 1)),

            Case ("multiplication", fn () =>
              A.raises "maxInt * 2" A.isOverflow (fn () => maxI () * 2)),

            Case ("negating minInt", fn () =>
              if maxI () + minI () = 0 then ()   (* symmetric range: no trap *)
              else A.raises "~minInt" A.isOverflow (fn () => ~(minI ()))),

            Case ("abs of minInt", fn () =>
              if maxI () + minI () = 0 then ()
              else A.raises "abs minInt" A.isOverflow (fn () => Int.abs (minI ()))),

            Case ("minInt div ~1", fn () =>
              if maxI () + minI () = 0 then ()
              else A.raises "minInt div ~1" A.isOverflow
                     (fn () => minI () div ~1)),

            Case ("minInt quot ~1", fn () =>
              if maxI () + minI () = 0 then ()
              else A.raises "minInt quot ~1" A.isOverflow
                     (fn () => Int.quot (minI (), A.hide ~1))),

            Case ("scanning a value too large to represent", fn () =>
              let
                val tooBig = Int.toString (maxI ()) ^ "0"
              in
                A.raises "fromString of an oversized literal" A.isOverflow
                  (fn () => Int.fromString tooBig)
              end),

            (* "This function raises Overflow when an integer can be parsed,
             * but is too large to be represented by type int" -- of scan, in
             * every radix, not only of fromString. *)
            Case ("scan of an oversized literal raises Overflow", fn () =>
              (A.raises "decimal" A.isOverflow
                 (fn () => scanDec (Int.fmt StringCvt.DEC (maxI ()) ^ "0"));
               A.raises "hexadecimal" A.isOverflow
                 (fn () => scanHex (Int.fmt StringCvt.HEX (maxI ()) ^ "0"));
               A.raises "octal" A.isOverflow
                 (fn () => scanOct (Int.fmt StringCvt.OCT (maxI ()) ^ "0"));
               A.raises "binary" A.isOverflow
                 (fn () => scanBin (Int.fmt StringCvt.BIN (maxI ()) ^ "0"))))
          ]),

        Group ("conversion to and from text",
        [ Case ("toString", fn () =>
            (A.eqString "zero" ("0", Int.toString 0);
             A.eqString "positive" ("42", Int.toString 42);
             A.eqString "negative uses a tilde" ("~42", Int.toString ~42))),

          (* The Basis grammar for integer scanning admits any of the three
           * signs [+~-], not just the ~ that toString emits. *)
          Case ("fromString accepts all three signs", fn () =>
            (A.eqIntOption "unsigned" (SOME 42, Int.fromString "42");
             A.eqIntOption "tilde" (SOME ~42, Int.fromString "~42");
             A.eqIntOption "hyphen" (SOME ~42, Int.fromString "-42");
             A.eqIntOption "plus" (SOME 42, Int.fromString "+42"))),

          Case ("fromString skips leading whitespace", fn () =>
            A.eqIntOption "spaces and a tab" (SOME 42, Int.fromString " \t 42")),

          Case ("fromString stops at the first non-digit", fn () =>
            (A.eqIntOption "trailing letters" (SOME 42, Int.fromString "42abc");
             A.eqIntOption "0x is not a decimal prefix"
               (SOME 0, Int.fromString "0x1F"))),

          Case ("fromString rejects non-numbers", fn () =>
            (A.eqIntOption "empty" (NONE, Int.fromString "");
             A.eqIntOption "letters" (NONE, Int.fromString "abc");
             A.eqIntOption "sign alone" (NONE, Int.fromString "~");
             A.eqIntOption "whitespace only" (NONE, Int.fromString "   "))),

          Case ("fmt in each radix", fn () =>
            (A.eqString "binary" ("101", Int.fmt StringCvt.BIN 5);
             A.eqString "octal" ("17", Int.fmt StringCvt.OCT 15);
             A.eqString "decimal" ("255", Int.fmt StringCvt.DEC 255);
             A.eqString "hexadecimal is upper case"
               ("FF", Int.fmt StringCvt.HEX 255);
             A.eqString "negative hexadecimal"
               ("~FF", Int.fmt StringCvt.HEX ~255))),

          Case ("scan in each radix", fn () =>
            (A.eqIntOption "binary" (SOME 5, scanBin "101");
             A.eqIntOption "octal" (SOME 15, scanOct "17");
             A.eqIntOption "decimal" (SOME 255, scanDec "255");
             A.eqIntOption "hexadecimal" (SOME 255, scanHex "FF");
             A.eqIntOption "lower case hexadecimal" (SOME 255, scanHex "ff"))),

          Case ("scan accepts the optional radix prefix", fn () =>
            (A.eqIntOption "0x" (SOME 31, scanHex "0x1F");
             A.eqIntOption "0X" (SOME 31, scanHex "0X1F");
             A.eqIntOption "no prefix" (SOME 31, scanHex "1F"))),

          Case ("scan stops at a digit outside the radix", fn () =>
            (A.eqIntOption "2 is not binary" (SOME 1, scanBin "12");
             A.eqIntOption "8 is not octal" (SOME 7, scanOct "78");
             A.eqIntOption "g is not hexadecimal" (SOME 15, scanHex "fg"))),

          (* "Note that strings such as "0xg" and "0x 123" are scanned as
           * SOME(0), even using a hexadecimal radix." -- the 0x is only a
           * prefix when a hexadecimal digit follows it; otherwise the 0 is
           * the number and the x is the first unconsumed character. *)
          Case ("an unfollowed 0x prefix scans as zero", fn () =>
            let
              fun scanRest s =
                case Int.scan StringCvt.HEX Substring.getc (Substring.full s) of
                    NONE => NONE
                  | SOME (n, rest) => SOME (n, Substring.string rest)
              val showIt = Show.option (Show.pair (Show.int, Show.string))
            in
              A.eqBy (op =, showIt) "0xg"
                (SOME (0, "xg"), scanRest "0xg");
              A.eqBy (op =, showIt) "0x 123"
                (SOME (0, "x 123"), scanRest "0x 123");
              A.eqBy (op =, showIt) "0x alone"
                (SOME (0, "x"), scanRest "0x");
              A.eqIntOption "through fromString-style scanning"
                (SOME 0, scanHex "0xg")
            end),

          Case ("scan skips leading whitespace in every radix", fn () =>
            (A.eqIntOption "binary" (SOME 5, scanBin "  \t101");
             A.eqIntOption "octal" (SOME 15, scanOct "\n 17");
             A.eqIntOption "decimal" (SOME 255, scanDec " \r\n255");
             A.eqIntOption "hexadecimal" (SOME 255, scanHex " \f\vFF"))),

          Case ("scan returns the unconsumed remainder", fn () =>
            case Int.scan StringCvt.DEC Substring.getc
                          (Substring.full "  42 rest") of
                NONE => A.fail "scan returned NONE"
              | SOME (n, rest) =>
                  (A.eqInt "value" (42, n);
                   A.eqString "remainder" (" rest", Substring.string rest)))
        ]),

        Group ("conversion to LargeInt",
        [ Case ("round trip through LargeInt", fn () =>
            (A.eqInt "positive" (42, Int.fromLarge (Int.toLarge 42));
             A.eqInt "negative" (~42, Int.fromLarge (Int.toLarge ~42));
             A.eqInt "zero" (0, Int.fromLarge (Int.toLarge 0)))),

          (* INTEGER requires toInt and fromInt even for Int itself, where
           * they are the identity. *)
          Case ("toInt and fromInt are the identity on Int", fn () =>
            (A.eqInt "toInt" (42, Int.toInt 42);
             A.eqInt "fromInt" (42, Int.fromInt 42);
             A.eqInt "a negative value" (~42, Int.toInt (Int.fromInt ~42)))),

          Case ("the bounds survive the round trip", fn () =>
            if not fixed then ()
            else
              (A.eqInt "maxInt" (maxI (), Int.fromLarge (Int.toLarge (maxI ())));
               A.eqInt "minInt" (minI (), Int.fromLarge (Int.toLarge (minI ())))))
        ]),

        Group ("laws",
        [ P.forAll ("addition commutes", smallPair, showPair,
                    fn (a, b) => a + b = b + a),

          P.forAll ("addition associates", smallTriple, showTriple,
                    fn (a, b, c) => (a + b) + c = a + (b + c)),

          P.forAll ("zero is a unit for addition", G.anyInt, Show.int,
                    fn a => a + 0 = a),

          P.forAll ("multiplication commutes", smallPair, showPair,
                    fn (a, b) => a * b = b * a),

          P.forAll ("multiplication distributes over addition",
                    smallTriple, showTriple,
                    fn (a, b, c) => a * (b + c) = a * b + a * c),

          P.forAll ("subtraction inverts addition", smallPair, showPair,
                    fn (a, b) => (a + b) - b = a),

          P.forAll ("negation is an involution", G.smallInt, Show.int,
                    fn a => ~(~a) = a),

          P.forAll ("div and mod reconstruct the dividend",
                    divisorPair, showPair,
                    fn (a, b) => (a div b) * b + (a mod b) = a),

          P.forAll ("mod is smaller in magnitude than the divisor",
                    divisorPair, showPair,
                    fn (a, b) => Int.abs (a mod b) < Int.abs b),

          P.forAll ("mod takes the sign of the divisor, or is zero",
                    divisorPair, showPair,
                    fn (a, b) =>
                      let val m = a mod b
                      in m = 0 orelse Int.sign m = Int.sign b end),

          P.forAll ("quot and rem reconstruct the dividend",
                    divisorPair, showPair,
                    fn (a, b) => Int.quot (a, b) * b + Int.rem (a, b) = a),

          P.forAll ("rem is smaller in magnitude than the divisor",
                    divisorPair, showPair,
                    fn (a, b) => Int.abs (Int.rem (a, b)) < Int.abs b),

          P.forAll ("rem takes the sign of the dividend, or is zero",
                    divisorPair, showPair,
                    fn (a, b) =>
                      let val m = Int.rem (a, b)
                      in m = 0 orelse Int.sign m = Int.sign a end),

          P.forAll ("div and quot agree when the signs agree",
                    divisorPair, showPair,
                    fn (a, b) =>
                      P.implies (Int.sameSign (a, b),
                                 a div b = Int.quot (a, b))),

          P.forAll ("compare agrees with the comparison operators",
                    G.pair (G.anyInt, G.anyInt), showPair,
                    fn (a, b) =>
                      case Int.compare (a, b) of
                          LESS => a < b
                        | EQUAL => a = b
                        | GREATER => a > b),

          P.forAll ("min and max bracket both arguments",
                    G.pair (G.anyInt, G.anyInt), showPair,
                    fn (a, b) =>
                      let
                        val lo = Int.min (a, b)
                        val hi = Int.max (a, b)
                      in
                        lo <= a andalso lo <= b andalso hi >= a andalso hi >= b
                        andalso (lo = a orelse lo = b)
                        andalso (hi = a orelse hi = b)
                      end),

          P.forAll ("abs is non-negative and preserves magnitude",
                    G.smallInt, Show.int,
                    fn a => Int.abs a >= 0 andalso (Int.abs a = a orelse Int.abs a = ~a)),

          P.forAll ("sign classifies", G.anyInt, Show.int,
                    fn a =>
                      case Int.sign a of
                          0 => a = 0
                        | 1 => a > 0
                        | ~1 => a < 0
                        | _ => false),

          P.forAll ("sameSign agrees with sign",
                    G.pair (G.anyInt, G.anyInt), showPair,
                    fn (a, b) => Int.sameSign (a, b) = (Int.sign a = Int.sign b)),

          P.forAll ("fromString inverts toString", G.anyInt, Show.int,
                    fn a => Int.fromString (Int.toString a) = SOME a),

          P.forAll ("scan inverts fmt in every radix", G.anyInt, Show.int,
                    fn a =>
                      List.all
                        (fn (radix, scan) => scan (Int.fmt radix a) = SOME a)
                        [ (StringCvt.BIN, scanBin),
                          (StringCvt.OCT, scanOct),
                          (StringCvt.DEC, scanDec),
                          (StringCvt.HEX, scanHex) ]),

          P.forAll ("LargeInt conversion round trips", G.anyInt, Show.int,
                    fn a => Int.fromLarge (Int.toLarge a) = a),

          (* "The second form is equivalent to fmt StringCvt.DEC i." *)
          P.forAll ("toString is fmt DEC", G.anyInt, Show.int,
                    fn a => Int.toString a = Int.fmt StringCvt.DEC a),

          (* "It is equivalent to the expression
           *  StringCvt.scanString (scan StringCvt.DEC)." *)
          P.forAll ("fromString is scanString of scan DEC",
                    G.oneOf [ G.map Int.toString G.anyInt,
                              G.printableString,
                              G.map (fn (a, s) => Int.toString a ^ s)
                                    (G.pair (G.anyInt, G.printableString)) ],
                    Show.string,
                    fn s =>
                      let
                        (* Both sides may legitimately raise Overflow on a
                         * generated literal too large for int; what is being
                         * checked is that they agree, exception included. *)
                        fun outcome f = SOME (f ()) handle Overflow => NONE
                      in
                        outcome (fn () => Int.fromString s)
                        = outcome (fn () =>
                            StringCvt.scanString (Int.scan StringCvt.DEC) s)
                      end),

          (* "returns the negation of i, i.e., (0 - i)" *)
          P.forAll ("negation is subtraction from zero", G.smallInt, Show.int,
                    fn a => ~a = 0 - a),

          P.forAll ("abs is the magnitude", G.smallInt, Show.int,
                    fn a => Int.abs a = (if a < 0 then ~a else a)),

          P.forAll ("the ordering operators agree with each other",
                    G.pair (G.anyInt, G.anyInt), showPair,
                    fn (a, b) =>
                      (a < b) = not (a >= b)
                      andalso (a > b) = not (a <= b)
                      andalso (a <= b) = (a < b orelse a = b)),

          P.forAll ("fmt DEC of a negative value is a tilde and the magnitude",
                    G.smallInt, Show.int,
                    fn a =>
                      P.implies (a < 0,
                                 Int.toString a = "~" ^ Int.toString (~a)))
        ])
      ])
  end
