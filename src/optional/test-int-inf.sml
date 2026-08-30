(* Tests for IntInf, the arbitrary precision integers.
 *
 * IntInf is an INTEGER, so the generic integer tests in gen-numeric.sml apply
 * to it unchanged and are instantiated for it alongside every other integer
 * instance.  What is tested here is the part of INT_INF that INTEGER does not
 * describe: unboundedness itself, divMod, quotRem, pow, log2, and the bitwise
 * operations, which are defined over the infinite two's complement
 * representation and so behave differently from a fixed-width word's.
 *
 * IntInf is optional, so this file is only reached through a build
 * description that names it; see build/optional/.
 *)

functor IntInfTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure II = IntInf

    val i = II.fromInt
    val showI = II.toString
    val eqI = A.eqBy (op =, showI)
    val eqIOpt = A.eqBy (op =, Show.option showI)
    val eqIPair = A.eqBy (op =, Show.pair (showI, showI))
    val showPair = Show.pair (showI, showI)

    val zero = i 0
    val one = i 1

    fun pow2 k = II.pow (i 2, k)

    (* Values far wider than any fixed precision integer: a list of six-digit
     * limbs, so the magnitude grows with the generator's size rather than
     * being pinned to one width. *)
    val genMagnitude =
      G.map (fn ns =>
               List.foldl (fn (n, acc) => II.+ (II.* (acc, i 1000000), i n))
                          zero ns)
            (G.list1 (G.int (0, 999999)))
    val genBig =
      G.map (fn (m, neg) => if neg then II.~ m else m)
            (G.pair (genMagnitude, G.bool))
    val genPositive = G.filter (fn x => II.> (x, zero)) genMagnitude
    val genNonZero = G.filter (fn x => x <> zero) genBig
    val genBigPair = G.pair (genBig, genBig)
    val genShift = G.map Word.fromInt (G.int (0, 200))
    val showShift = Show.word

    (* 2^100, written out, so that a system whose IntInf silently truncates is
     * caught against a constant rather than against itself. *)
    val twoTo100 = "1267650600228229401496703205376"

    (* Whether the default Int is itself unbounded.  Poly/ML and Moscow ML
     * have made Int arbitrary precision in the past, and there IntInf.toInt
     * never overflows, so the range test has to ask rather than assume. *)
    val intIsBounded = Option.isSome Int.precision

    val radices = [StringCvt.BIN, StringCvt.OCT, StringCvt.DEC, StringCvt.HEX]

    val suite = Group ("IntInf",
      [ Case ("the type is unbounded", fn () =>
          (A.eqIntOption "precision is NONE" (NONE, II.precision);
           A.that "maxInt is NONE" (not (Option.isSome II.maxInt));
           A.that "minInt is NONE" (not (Option.isSome II.minInt)))),

        Case ("arithmetic does not overflow", fn () =>
          let
            val big = pow2 200
          in
            A.noRaise "squaring a 200-bit value" (fn () => II.* (big, big));
            eqI "and the square is 2^400" (pow2 400, II.* (big, big));
            A.noRaise "adding one to it" (fn () => II.+ (big, one));
            A.eqString "2^100 has the expected decimal form"
              (twoTo100, II.toString (pow2 100));
            A.eqInt "and 2^1000 has 302 decimal digits"
              (302, String.size (II.toString (pow2 1000)))
          end),

        Case ("conversion to and from the fixed size integers", fn () =>
          (A.eqInt "toInt of a small value" (42, II.toInt (i 42));
           A.eqInt "toInt inverts fromInt" (~42, II.toInt (II.fromInt ~42));
           A.eqBy (op =, LargeInt.toString) "toLarge"
             (LargeInt.fromInt 42, II.toLarge (i 42));
           eqI "fromLarge" (i 42, II.fromLarge (LargeInt.fromInt 42));
           if intIsBounded then
             (A.raises "toInt of a value above maxInt" A.isOverflow
                (fn () => II.toInt (II.+ (II.fromInt (valOf Int.maxInt), one)));
              A.raises "toInt of a value below minInt" A.isOverflow
                (fn () => II.toInt (II.- (II.fromInt (valOf Int.minInt), one))))
           else
             A.noRaise "Int is itself unbounded, so nothing is out of range"
               (fn () => II.toInt (pow2 200)))),

        Case ("divMod and quotRem package the two rounding conventions",
              fn () =>
          (eqIPair "divMod rounds towards negative infinity"
             ((i ~4, i 1), II.divMod (i ~7, i 2));
           eqIPair "quotRem rounds towards zero"
             ((i ~3, i ~1), II.quotRem (i ~7, i 2));
           eqIPair "divMod of a positive pair" ((i 3, i 1), II.divMod (i 7, i 2));
           eqIPair "quotRem of a positive pair" ((i 3, i 1), II.quotRem (i 7, i 2));
           eqIPair "divMod by a negative divisor"
             ((i ~4, i ~1), II.divMod (i 7, i ~2));
           eqIPair "quotRem by a negative divisor"
             ((i ~3, i 1), II.quotRem (i 7, i ~2));
           A.raises "divMod by zero" A.isDiv (fn () => II.divMod (one, zero));
           A.raises "quotRem by zero" A.isDiv (fn () => II.quotRem (one, zero)))),

        Case ("pow", fn () =>
          (eqI "a positive exponent" (i 1024, II.pow (i 2, 10));
           eqI "a negative base, odd exponent" (i ~8, II.pow (i ~2, 3));
           eqI "a negative base, even exponent" (i 16, II.pow (i ~2, 4));
           eqI "exponent zero is one" (one, II.pow (i 7, 0));
           eqI "zero to the zero is one" (one, II.pow (zero, 0));
           eqI "zero to a positive exponent" (zero, II.pow (zero, 5));
           eqI "one to any exponent" (one, II.pow (one, 1000));
           A.eqString "a large exponent" (twoTo100, II.toString (II.pow (i 2, 100))))),

        (* The specification fixes pow at a negative exponent by cases rather
         * than leaving it undefined, and the cases are easy to get wrong. *)
        Case ("pow at a negative exponent", fn () =>
          (A.raises "zero base raises Div" A.isDiv (fn () => II.pow (zero, ~1));
           eqI "one to a negative exponent" (one, II.pow (one, ~5));
           eqI "minus one to an odd negative exponent" (i ~1, II.pow (i ~1, ~5));
           eqI "minus one to an even negative exponent" (one, II.pow (i ~1, ~4));
           eqI "a base above one truncates to zero" (zero, II.pow (i 2, ~1));
           eqI "a base below minus one truncates to zero"
             (zero, II.pow (i ~2, ~3)))),

        Case ("log2", fn () =>
          (A.eqInt "of one" (0, II.log2 one);
           A.eqInt "of two" (1, II.log2 (i 2));
           A.eqInt "rounds down" (1, II.log2 (i 3));
           A.eqInt "of a power of two" (100, II.log2 (pow2 100));
           A.eqInt "of one less than a power of two"
             (99, II.log2 (II.- (pow2 100, one)));
           A.raises "of zero" A.isDomain (fn () => II.log2 zero);
           A.raises "of a negative value" A.isDomain (fn () => II.log2 (i ~1)))),

        (* The bitwise operations are defined over the infinite two's
         * complement representation, so a negative value behaves as though it
         * had infinitely many leading one bits. *)
        Case ("bitwise operations on non-negative values", fn () =>
          (eqI "andb" (i 8, II.andb (i 12, i 10));
           eqI "orb" (i 14, II.orb (i 12, i 10));
           eqI "xorb" (i 6, II.xorb (i 12, i 10));
           eqI "notb of zero" (i ~1, II.notb zero);
           eqI "notb of five" (i ~6, II.notb (i 5)))),

        Case ("bitwise operations extend the sign infinitely", fn () =>
          (eqI "andb with minus one is the identity" (i 12, II.andb (i ~1, i 12));
           eqI "orb with minus one is minus one" (i ~1, II.orb (i ~1, i 12));
           eqI "andb of a negative and a positive" (i 2, II.andb (i ~2, i 3));
           eqI "andb of two negatives" (i ~4, II.andb (i ~2, i ~3));
           eqI "orb of two negatives" (i ~1, II.orb (i ~2, i ~3));
           eqI "xorb of two negatives" (i 3, II.xorb (i ~2, i ~3));
           eqI "xorb of a negative and a positive" (i ~4, II.xorb (i ~2, i 2));
           eqI "notb of minus one" (zero, II.notb (i ~1)))),

        Case ("bitwise operations reach past any fixed width", fn () =>
          let
            val hi = pow2 200
          in
            eqI "andb selects a high bit" (hi, II.andb (hi, II.- (pow2 201, one)));
            eqI "orb sets a high bit" (II.+ (hi, one), II.orb (hi, one));
            eqI "xorb clears a high bit" (zero, II.xorb (hi, hi));
            A.eqInt "and the result is still 200 bits wide"
              (200, II.log2 (II.orb (hi, one)))
          end),

        Case ("shifting", fn () =>
          (eqI "left by ten" (i 1024, II.<< (one, 0w10));
           eqI "left by zero" (i 7, II.<< (i 7, 0w0));
           eqI "left of a negative value" (i ~16, II.<< (i ~1, 0w4));
           eqI "left past any fixed width" (pow2 200, II.<< (one, 0w200));
           eqI "right by ten" (one, II.~>> (i 1024, 0w10));
           eqI "right rounds towards negative infinity" (i ~3, II.~>> (i ~5, 0w1));
           eqI "right of a positive value past its width" (zero, II.~>> (one, 0w200));
           eqI "right of a negative value past its width"
             (i ~1, II.~>> (i ~1, 0w200)))),

        Case ("text conversion at arbitrary size", fn () =>
          let
            val big = pow2 100
            val neg = II.~ big
          in
            eqIOpt "fromString reads a thirty-one digit number"
              (SOME big, II.fromString twoTo100);
            A.eqString "toString writes it back" (twoTo100, II.toString big);
            A.eqString "a negative value uses a tilde"
              ("~" ^ twoTo100, II.toString neg);
            eqIOpt "fromString accepts a hyphen" (SOME neg, II.fromString ("-" ^ twoTo100));
            A.eqString "fmt in hexadecimal"
              ("1" ^ String.implode (List.tabulate (25, fn _ => #"0")),
               II.fmt StringCvt.HEX big);
            eqIOpt "scan in hexadecimal"
              (SOME big,
               StringCvt.scanString (II.scan StringCvt.HEX) (II.fmt StringCvt.HEX big));
            A.eqString "fmt in binary"
              ("1" ^ String.implode (List.tabulate (100, fn _ => #"0")),
               II.fmt StringCvt.BIN big)
          end),

        Case ("comparison at arbitrary size", fn () =>
          let
            val big = pow2 200
          in
            A.eqOrder "a wide value against a narrow one"
              (GREATER, II.compare (big, i 1));
            A.eqOrder "against its own successor"
              (LESS, II.compare (big, II.+ (big, one)));
            A.eqOrder "a negative against a positive"
              (LESS, II.compare (II.~ big, big));
            A.eqInt "sign of a wide negative value" (~1, II.sign (II.~ big));
            eqI "abs of a wide negative value" (big, II.abs (II.~ big));
            A.eqBool "sameSign" (true, II.sameSign (II.~ big, i ~1))
          end),

        P.forAll ("toString and fromString round trip at any size",
                  genBig, showI,
                  fn a => II.fromString (II.toString a) = SOME a),

        P.forAll ("scan inverts fmt in every radix at any size", genBig, showI,
                  fn a =>
                    List.all
                      (fn radix =>
                         StringCvt.scanString (II.scan radix) (II.fmt radix a)
                         = SOME a)
                      radices),

        P.forAll ("divMod is div paired with mod",
                  G.pair (genBig, genNonZero), showPair,
                  fn (a, b) => II.divMod (a, b) = (II.div (a, b), II.mod (a, b))),

        P.forAll ("quotRem is quot paired with rem",
                  G.pair (genBig, genNonZero), showPair,
                  fn (a, b) => II.quotRem (a, b) = (II.quot (a, b), II.rem (a, b))),

        P.forAll ("divMod reconstructs the dividend",
                  G.pair (genBig, genNonZero), showPair,
                  fn (a, b) =>
                    let val (q, m) = II.divMod (a, b)
                    in II.+ (II.* (q, b), m) = a end),

        P.forAll ("quotRem reconstructs the dividend",
                  G.pair (genBig, genNonZero), showPair,
                  fn (a, b) =>
                    let val (q, r) = II.quotRem (a, b)
                    in II.+ (II.* (q, b), r) = a end),

        P.forAll ("pow agrees with repeated multiplication",
                  G.pair (G.map i (G.int (~20, 20)), G.int (0, 12)),
                  Show.pair (showI, Show.int),
                  fn (a, k) =>
                    let
                      fun times (_, 0, acc) = acc
                        | times (x, j, acc) = times (x, j - 1, II.* (acc, x))
                    in
                      II.pow (a, k) = times (a, k, one)
                    end),

        P.forAll ("pow adds exponents",
                  G.triple (G.map i (G.int (~9, 9)), G.int (0, 20), G.int (0, 20)),
                  Show.triple (showI, Show.int, Show.int),
                  fn (a, j, k) =>
                    II.pow (a, j + k) = II.* (II.pow (a, j), II.pow (a, k))),

        P.forAll ("log2 brackets the value between two powers of two",
                  genPositive, showI,
                  fn a =>
                    let val k = II.log2 a
                    in II.<= (pow2 k, a) andalso II.< (a, pow2 (k + 1)) end),

        P.forAll ("log2 of a power of two is its exponent", G.int (0, 300),
                  Show.int,
                  fn k => II.log2 (pow2 k) = k),

        P.forAll ("notb is the negated successor", genBig, showI,
                  fn a => II.notb a = II.~ (II.+ (a, one))),

        P.forAll ("notb is its own inverse", genBig, showI,
                  fn a => II.notb (II.notb a) = a),

        P.forAll ("xorb with itself clears every bit", genBig, showI,
                  fn a => II.xorb (a, a) = zero),

        P.forAll ("a value and its complement share no bits", genBig, showI,
                  fn a =>
                    II.andb (a, II.notb a) = zero
                    andalso II.orb (a, II.notb a) = i ~1),

        P.forAll ("andb and orb are idempotent", genBig, showI,
                  fn a => II.andb (a, a) = a andalso II.orb (a, a) = a),

        P.forAll ("De Morgan's laws hold over the infinite representation",
                  genBigPair, showPair,
                  fn (a, b) =>
                    II.notb (II.andb (a, b))
                    = II.orb (II.notb a, II.notb b)
                    andalso II.notb (II.orb (a, b))
                            = II.andb (II.notb a, II.notb b)),

        P.forAll ("xorb is addition without carries",
                  genBigPair, showPair,
                  fn (a, b) =>
                    II.xorb (a, b)
                    = II.- (II.orb (a, b), II.andb (a, b))),

        P.forAll ("a left shift multiplies by a power of two",
                  G.pair (genBig, genShift), Show.pair (showI, showShift),
                  fn (a, w) =>
                    II.<< (a, w) = II.* (a, pow2 (Word.toInt w))),

        P.forAll ("an arithmetic right shift divides by a power of two",
                  G.pair (genBig, genShift), Show.pair (showI, showShift),
                  fn (a, w) =>
                    II.~>> (a, w) = II.div (a, pow2 (Word.toInt w))),

        P.forAll ("a right shift undoes a left shift",
                  G.pair (genBig, genShift), Show.pair (showI, showShift),
                  fn (a, w) => II.~>> (II.<< (a, w), w) = a),

        P.forAll ("the fixed size integers round trip when they fit",
                  G.anyInt, Show.int,
                  fn n => II.toInt (II.fromInt n) = n),

        P.forAll ("toInt raises Overflow exactly when the value does not fit",
                  genBig, showI,
                  fn a =>
                    P.impliesBy (intIsBounded, fn () =>
                      let
                        val fits =
                          II.<= (a, II.fromInt (valOf Int.maxInt))
                          andalso II.>= (a, II.fromInt (valOf Int.minInt))
                      in
                        if fits
                        then II.fromInt (II.toInt a) = a
                        else ((ignore (II.toInt a); false)
                              handle Overflow => true)
                      end))
      ])
  end
