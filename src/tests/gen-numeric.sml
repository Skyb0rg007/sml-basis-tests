(* Generic tests for the numeric signatures, instantiated for every required
 * instance: WORD for Word, Word8 and LargeWord; INTEGER for Int, LargeInt and
 * Position; REAL for Real and LargeReal.
 *
 * Each instance is a separate implementation with its own width, so nothing
 * here hard-codes one: boundary values are derived from wordSize or precision
 * at run time, exactly as in the hand-written Word and Int suites.  Those
 * remain, and go deeper on the default types; these give breadth across every
 * instance the Basis requires.
 *)

functor WordInstanceTestsFn (structure W : WORD
                             val name : string) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val ws = W.wordSize
    val zero = W.fromInt 0
    val one = W.fromInt 1
    val allOnes = W.notb zero
    val topBit = W.<< (one, Word.fromInt (ws - 1))
    val past = Word.fromInt ws

    fun showW w = "0wx" ^ W.toString w
    val eqW = A.eqBy (op =, showW)
    val eqWOpt = A.eqBy (op =, Show.option showW)
    fun w n = W.fromInt n

    (* Values built from ints stay inside every instance's range, Word8
     * included, so the same generator serves all three. *)
    val small = G.map w (G.int (0, 255))
    val genW =
      G.map (fn ns => List.foldl (fn (n, acc) => W.orb (W.<< (acc, 0w8), w n))
                                 zero ns)
            (G.listN ((ws + 7) div 8) (G.int (0, 255)))
    val pairW = G.pair (genW, genW)
    val showPair = Show.pair (showW, showW)
    val nonZero = G.filter (fn x => x <> zero) genW

    val scanDec = StringCvt.scanString (W.scan StringCvt.DEC)
    val scanHex = StringCvt.scanString (W.scan StringCvt.HEX)

    (* toIntX yields a signed value of this word's width, which only fits in an
     * int when the int is at least as wide -- LargeWord on a 64-bit system is
     * wider than the default int, so the round trip through int is not
     * available there. *)
    val signedFitsInInt =
      case Int.precision of
          NONE => true
        | SOME p => ws <= p

    val suite = Group (name,
      [ Case ("width", fn () =>
          (A.that "wordSize is positive" (ws > 0);
           eqW "all ones plus one wraps to zero" (zero, W.+ (allOnes, one));
           eqW "the top bit doubled wraps to zero" (zero, W.+ (topBit, topBit)))),

        Case ("arithmetic wraps rather than trapping", fn () =>
          (eqW "subtraction wraps" (allOnes, W.- (zero, one));
           eqW "multiplication wraps" (one, W.* (allOnes, allOnes));
           eqW "negation of zero" (zero, W.~ zero);
           eqW "negation of one" (allOnes, W.~ one);
           A.noRaise "no overflow" (fn () => W.* (allOnes, allOnes)))),

        Case ("division", fn () =>
          (eqW "div" (w 3, W.div (w 7, w 2));
           eqW "mod" (w 1, W.mod (w 7, w 2));
           A.raises "div by zero" A.isDiv (fn () => W.div (one, zero));
           A.raises "mod by zero" A.isDiv (fn () => W.mod (one, zero)))),

        Case ("bitwise operations", fn () =>
          (eqW "andb" (w 8, W.andb (w 12, w 10));
           eqW "orb" (w 14, W.orb (w 12, w 10));
           eqW "xorb" (w 6, W.xorb (w 12, w 10));
           eqW "notb of zero" (allOnes, W.notb zero);
           eqW "notb of all ones" (zero, W.notb allOnes))),

        Case ("shifting past the width", fn () =>
          (eqW "left" (zero, W.<< (allOnes, past));
           eqW "left, well past" (zero, W.<< (allOnes, Word.fromInt (ws + 5)));
           eqW "logical right" (zero, W.>> (allOnes, past));
           eqW "arithmetic right of a negative pattern"
             (allOnes, W.~>> (allOnes, past));
           eqW "arithmetic right of a positive pattern" (zero, W.~>> (one, past));
           eqW "the top bit propagates"
             (allOnes, W.~>> (topBit, Word.fromInt (ws - 1))))),

        Case ("comparison is unsigned", fn () =>
          (A.eqBool "all ones is large, not negative" (true, W.> (allOnes, one));
           A.eqOrder "compare" (GREATER, W.compare (allOnes, one));
           A.eqBool "less" (true, W.< (one, allOnes));
           A.eqBool "less or equal" (true, W.<= (one, one));
           A.eqBool "greater or equal" (true, W.>= (one, one));
           eqW "min" (one, W.min (one, allOnes));
           eqW "max" (allOnes, W.max (one, allOnes)))),

        Case ("conversion to and from int", fn () =>
          (eqW "fromInt of a negative int wraps" (allOnes, W.fromInt ~1);
           A.eqInt "toIntX of all ones" (~1, W.toIntX allOnes);
           A.eqInt "toIntX of zero" (0, W.toIntX zero);
           A.eqInt "toInt of a small value" (5, W.toInt (w 5)))),

        Case ("conversion through the large types", fn () =>
          (A.eqBy (op =, LargeWord.toString) "toLarge of a small value"
             (LargeWord.fromInt 5, W.toLarge (w 5));
           eqW "fromLarge inverts toLarge" (w 5, W.fromLarge (W.toLarge (w 5)));
           A.eqBy (op =, LargeInt.toString) "toLargeInt"
             (LargeInt.fromInt 5, W.toLargeInt (w 5));
           A.eqBy (op =, LargeInt.toString) "toLargeIntX of all ones"
             (LargeInt.fromInt ~1, W.toLargeIntX allOnes);
           eqW "fromLargeInt" (w 5, W.fromLargeInt (LargeInt.fromInt 5)))),

        (* toLarge zero-extends, toLargeX propagates the sign bit. *)
        Case ("toLarge and toLargeX differ on a negative pattern", fn () =>
          if ws = LargeWord.wordSize then
            A.eqBy (op =, LargeWord.toString) "at equal widths they agree"
              (W.toLarge allOnes, W.toLargeX allOnes)
          else
            (A.eqBy (op =, LargeWord.toString) "toLargeX fills the top with ones"
               (LargeWord.notb (LargeWord.fromInt 0), W.toLargeX allOnes);
             A.that "toLarge does not"
               (W.toLarge allOnes <> W.toLargeX allOnes))),

        (* The 2004 Basis still lists the older spellings alongside the new. *)
        Case ("the deprecated aliases agree with the current names", fn () =>
          (A.eqBy (op =, LargeWord.toString) "toLargeWord is toLarge"
             (W.toLarge (w 5), W.toLargeWord (w 5));
           A.eqBy (op =, LargeWord.toString) "toLargeWordX is toLargeX"
             (W.toLargeX allOnes, W.toLargeWordX allOnes);
           eqW "fromLargeWord is fromLarge"
             (W.fromLarge (W.toLarge (w 5)), W.fromLargeWord (W.toLarge (w 5))))),

        Case ("conversion to and from text", fn () =>
          (A.eqString "toString is upper-case hexadecimal" ("FF", W.toString (w 255));
           A.eqString "zero" ("0", W.toString zero);
           eqWOpt "fromString" (SOME (w 255), W.fromString "FF");
           eqWOpt "fromString, lower case" (SOME (w 255), W.fromString "ff");
           eqWOpt "fromString with the 0x prefix" (SOME (w 255), W.fromString "0xFF");
           eqWOpt "fromString rejects letters" (NONE, W.fromString "zz");
           A.eqString "fmt binary" ("101", W.fmt StringCvt.BIN (w 5));
           A.eqString "fmt octal" ("17", W.fmt StringCvt.OCT (w 15));
           A.eqString "fmt decimal" ("255", W.fmt StringCvt.DEC (w 255));
           A.eqString "fmt hexadecimal" ("FF", W.fmt StringCvt.HEX (w 255));
           eqWOpt "scan decimal" (SOME (w 255), scanDec "255");
           eqWOpt "scan hexadecimal" (SOME (w 255), scanHex "FF");
           eqWOpt "scan rejects a sign" (NONE, scanDec "~1"))),

        P.forAll ("addition commutes", pairW, showPair,
                  fn (a, b) => W.+ (a, b) = W.+ (b, a)),

        P.forAll ("multiplication commutes", pairW, showPair,
                  fn (a, b) => W.* (a, b) = W.* (b, a)),

        P.forAll ("subtraction inverts addition", pairW, showPair,
                  fn (a, b) => W.- (W.+ (a, b), b) = a),

        P.forAll ("notb is an involution", genW, showW,
                  fn a => W.notb (W.notb a) = a),

        P.forAll ("xorb with itself annihilates", genW, showW,
                  fn a => W.xorb (a, a) = zero),

        P.forAll ("de Morgan", pairW, showPair,
                  fn (a, b) =>
                    W.notb (W.andb (a, b)) = W.orb (W.notb a, W.notb b)),

        P.forAll ("shifting left then right clears the high bits",
                  G.pair (genW, G.map Word.fromInt (G.int (0, ws + 2))),
                  Show.pair (showW, Show.word),
                  fn (a, k) =>
                    W.>> (W.<< (a, k), k) = W.andb (a, W.>> (allOnes, k))),

        P.forAll ("div and mod reconstruct the dividend",
                  G.pair (genW, nonZero), showPair,
                  fn (a, b) => W.+ (W.* (W.div (a, b), b), W.mod (a, b)) = a),

        P.forAll ("mod is smaller than the divisor",
                  G.pair (genW, nonZero), showPair,
                  fn (a, b) => W.< (W.mod (a, b), b)),

        P.forAll ("compare agrees with the operators", pairW, showPair,
                  fn (a, b) =>
                    case W.compare (a, b) of
                        LESS => W.< (a, b)
                      | EQUAL => a = b
                      | GREATER => W.> (a, b)),

        P.forAll ("fromString inverts toString", genW, showW,
                  fn a => W.fromString (W.toString a) = SOME a),

        P.forAll ("scan inverts fmt in every radix", genW, showW,
                  fn a =>
                    List.all
                      (fn (radix, scan) => scan (W.fmt radix a) = SOME a)
                      [ (StringCvt.BIN, StringCvt.scanString (W.scan StringCvt.BIN)),
                        (StringCvt.OCT, StringCvt.scanString (W.scan StringCvt.OCT)),
                        (StringCvt.DEC, scanDec),
                        (StringCvt.HEX, scanHex) ]),

        P.forAll ("fromInt inverts toIntX where the int is wide enough",
                  genW, showW,
                  fn a =>
                    (* Deferred: toIntX itself overflows when the int is
                     * narrower than this word. *)
                    P.impliesBy (signedFitsInInt,
                                 fn () => W.fromInt (W.toIntX a) = a)),

        P.forAll ("fromLarge inverts toLarge", genW, showW,
                  fn a => W.fromLarge (W.toLarge a) = a),

        P.forAll ("fromLargeInt inverts toLargeIntX", genW, showW,
                  fn a => W.fromLargeInt (W.toLargeIntX a) = a)
      ])
  end

functor IntegerInstanceTestsFn (structure I : INTEGER
                                val name : string) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val i = I.fromInt
    val showI = I.toString
    val eqI = A.eqBy (op =, showI)
    val eqIOpt = A.eqBy (op =, Show.option showI)
    val fixed = Option.isSome I.precision

    (* Small enough that every required instance can hold the results. *)
    val genI = G.map i (G.int (~10000, 10000))
    val pairI = G.pair (genI, genI)
    val showPair = Show.pair (showI, showI)
    val nonZero = G.filter (fn x => x <> i 0) genI

    val suite = Group (name,
      [ Case ("range", fn () =>
          (A.eqBool "precision, minInt and maxInt agree about being bounded"
             (fixed, Option.isSome I.maxInt andalso Option.isSome I.minInt);
           if not fixed then ()
           else
             (A.that "maxInt is positive" (I.> (valOf I.maxInt, i 0));
              A.that "minInt is negative" (I.< (valOf I.minInt, i 0));
              let val s = I.+ (valOf I.maxInt, valOf I.minInt)
              in A.that "the bounds are symmetric to within one"
                        (s = i 0 orelse s = i ~1)
              end))),

        Case ("arithmetic", fn () =>
          (eqI "addition" (i 5, I.+ (i 2, i 3));
           eqI "subtraction" (i ~1, I.- (i 2, i 3));
           eqI "multiplication" (i 6, I.* (i 2, i 3));
           eqI "negation" (i ~2, I.~ (i 2));
           eqI "absolute value" (i 2, I.abs (i ~2));
           eqI "min" (i 2, I.min (i 2, i 3));
           eqI "max" (i 3, I.max (i 2, i 3)))),

        Case ("sign", fn () =>
          (A.eqInt "positive" (1, I.sign (i 5));
           A.eqInt "negative" (~1, I.sign (i ~5));
           A.eqInt "zero" (0, I.sign (i 0));
           A.eqBool "sameSign" (true, I.sameSign (i ~1, i ~2));
           A.eqBool "different signs" (false, I.sameSign (i ~1, i 2)))),

        Case ("div and mod round towards negative infinity", fn () =>
          (eqI "7 div 2" (i 3, I.div (i 7, i 2));
           eqI "~7 div 2" (i ~4, I.div (i ~7, i 2));
           eqI "7 div ~2" (i ~4, I.div (i 7, i ~2));
           eqI "~7 div ~2" (i 3, I.div (i ~7, i ~2));
           eqI "7 mod 2" (i 1, I.mod (i 7, i 2));
           eqI "~7 mod 2" (i 1, I.mod (i ~7, i 2));
           eqI "7 mod ~2" (i ~1, I.mod (i 7, i ~2));
           eqI "~7 mod ~2" (i ~1, I.mod (i ~7, i ~2)))),

        Case ("quot and rem round towards zero", fn () =>
          (eqI "7 quot 2" (i 3, I.quot (i 7, i 2));
           eqI "~7 quot 2" (i ~3, I.quot (i ~7, i 2));
           eqI "7 quot ~2" (i ~3, I.quot (i 7, i ~2));
           eqI "~7 quot ~2" (i 3, I.quot (i ~7, i ~2));
           eqI "7 rem 2" (i 1, I.rem (i 7, i 2));
           eqI "~7 rem 2" (i ~1, I.rem (i ~7, i 2));
           eqI "7 rem ~2" (i 1, I.rem (i 7, i ~2));
           eqI "~7 rem ~2" (i ~1, I.rem (i ~7, i ~2)))),

        Case ("division by zero", fn () =>
          (A.raises "div" A.isDiv (fn () => I.div (i 1, i 0));
           A.raises "mod" A.isDiv (fn () => I.mod (i 1, i 0));
           A.raises "quot" A.isDiv (fn () => I.quot (i 1, i 0));
           A.raises "rem" A.isDiv (fn () => I.rem (i 1, i 0)))),

        Case ("comparison", fn () =>
          (A.eqOrder "less" (LESS, I.compare (i 1, i 2));
           A.eqOrder "equal" (EQUAL, I.compare (i 2, i 2));
           A.eqOrder "greater" (GREATER, I.compare (i 3, i 2));
           A.eqBool "less" (true, I.< (i 1, i 2));
           A.eqBool "less or equal" (true, I.<= (i 2, i 2));
           A.eqBool "greater" (true, I.> (i 3, i 2));
           A.eqBool "greater or equal" (true, I.>= (i 2, i 2)))),

        Case ("conversion to and from text", fn () =>
          (A.eqString "toString" ("42", I.toString (i 42));
           A.eqString "negative uses a tilde" ("~42", I.toString (i ~42));
           eqIOpt "fromString" (SOME (i 42), I.fromString "42");
           eqIOpt "fromString with a tilde" (SOME (i ~42), I.fromString "~42");
           eqIOpt "fromString with a hyphen" (SOME (i ~42), I.fromString "-42");
           eqIOpt "fromString rejects letters" (NONE, I.fromString "abc");
           A.eqString "fmt binary" ("101", I.fmt StringCvt.BIN (i 5));
           A.eqString "fmt octal" ("17", I.fmt StringCvt.OCT (i 15));
           A.eqString "fmt decimal" ("255", I.fmt StringCvt.DEC (i 255));
           A.eqString "fmt hexadecimal is upper case"
             ("FF", I.fmt StringCvt.HEX (i 255));
           eqIOpt "scan hexadecimal"
             (SOME (i 255), StringCvt.scanString (I.scan StringCvt.HEX) "FF"))),

        Case ("conversion through the large type", fn () =>
          (A.eqBy (op =, LargeInt.toString) "toLarge"
             (LargeInt.fromInt 42, I.toLarge (i 42));
           eqI "fromLarge" (i 42, I.fromLarge (LargeInt.fromInt 42));
           A.eqInt "toInt" (42, I.toInt (i 42));
           eqI "fromInt" (i 42, I.fromInt 42))),

        P.forAll ("addition commutes", pairI, showPair,
                  fn (a, b) => I.+ (a, b) = I.+ (b, a)),

        P.forAll ("multiplication distributes over addition",
                  G.triple (genI, genI, genI),
                  Show.triple (showI, showI, showI),
                  fn (a, b, c) =>
                    I.* (a, I.+ (b, c)) = I.+ (I.* (a, b), I.* (a, c))),

        P.forAll ("subtraction inverts addition", pairI, showPair,
                  fn (a, b) => I.- (I.+ (a, b), b) = a),

        P.forAll ("div and mod reconstruct the dividend",
                  G.pair (genI, nonZero), showPair,
                  fn (a, b) => I.+ (I.* (I.div (a, b), b), I.mod (a, b)) = a),

        P.forAll ("mod is smaller in magnitude than the divisor",
                  G.pair (genI, nonZero), showPair,
                  fn (a, b) => I.< (I.abs (I.mod (a, b)), I.abs b)),

        P.forAll ("mod takes the sign of the divisor, or is zero",
                  G.pair (genI, nonZero), showPair,
                  fn (a, b) =>
                    let val m = I.mod (a, b)
                    in m = i 0 orelse I.sign m = I.sign b end),

        P.forAll ("quot and rem reconstruct the dividend",
                  G.pair (genI, nonZero), showPair,
                  fn (a, b) => I.+ (I.* (I.quot (a, b), b), I.rem (a, b)) = a),

        P.forAll ("rem takes the sign of the dividend, or is zero",
                  G.pair (genI, nonZero), showPair,
                  fn (a, b) =>
                    let val m = I.rem (a, b)
                    in m = i 0 orelse I.sign m = I.sign a end),

        P.forAll ("compare agrees with the operators", pairI, showPair,
                  fn (a, b) =>
                    case I.compare (a, b) of
                        LESS => I.< (a, b)
                      | EQUAL => a = b
                      | GREATER => I.> (a, b)),

        P.forAll ("abs is non-negative", genI, showI,
                  fn a => I.>= (I.abs a, i 0)),

        P.forAll ("fromString inverts toString", genI, showI,
                  fn a => I.fromString (I.toString a) = SOME a),

        P.forAll ("scan inverts fmt in every radix", genI, showI,
                  fn a =>
                    List.all
                      (fn radix =>
                         StringCvt.scanString (I.scan radix) (I.fmt radix a)
                         = SOME a)
                      [StringCvt.BIN, StringCvt.OCT, StringCvt.DEC, StringCvt.HEX]),

        P.forAll ("the large type round trips", genI, showI,
                  fn a => I.fromLarge (I.toLarge a) = a),

        P.forAll ("int round trips", G.int (~10000, 10000), Show.int,
                  fn n => I.toInt (I.fromInt n) = n)
      ])
  end

functor RealInstanceTestsFn (structure R : REAL
                             val name : string
                             val ieee : bool) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val r = R.fromInt
    fun showR x = R.fmt StringCvt.EXACT x
    fun eqR msg (e, a) =
      if R.== (e, a) then ()
      else A.fail (msg ^ ": expected " ^ showR e ^ " but got " ^ showR a)
    fun nan () = R./ (r 0, r 0)
    fun negZero () = R.~ (r 0)

    (* One ulp, derived from the instance's own precision. *)
    val ulp =
      let fun half (x, 0) = x | half (x, n) = half (R./ (x, r 2), n - 1)
      in half (r 1, R.precision - 1) end

    fun near msg (e, a) =
      let val tol = R.* (ulp, r 1024)
      in
        if R.== (e, a)
           orelse R.<= (R.abs (R.- (e, a)),
                        R.* (tol, R.max (R.abs e, r 1)))
        then ()
        else A.fail (msg ^ ": expected " ^ showR e ^ " but got " ^ showR a)
      end

    fun className IEEEReal.NAN = "NAN" | className IEEEReal.INF = "INF"
      | className IEEEReal.ZERO = "ZERO" | className IEEEReal.NORMAL = "NORMAL"
      | className IEEEReal.SUBNORMAL = "SUBNORMAL"
    val eqCls = A.eqBy (op =, className)

    val genR = G.map (fn n => R./ (r n, r 7)) (G.int (~10000, 10000))
    val pairR = G.pair (genR, genR)
    val showPair = Show.pair (showR, showR)

    val suite = Group (name,
      [ Case ("format parameters", fn () =>
          (A.that "radix is at least two" (R.radix >= 2);
           A.that "precision is positive" (R.precision > 0);
           A.that "minPos is positive" (R.> (R.minPos, r 0));
           A.that "minPos does not exceed minNormalPos"
             (R.<= (R.minPos, R.minNormalPos));
           A.that "minNormalPos is below maxFinite"
             (R.< (R.minNormalPos, R.maxFinite));
           A.that "maxFinite is finite" (R.isFinite R.maxFinite))),

        Case ("arithmetic", fn () =>
          (eqR "addition" (r 5, R.+ (r 2, r 3));
           eqR "subtraction" (r ~1, R.- (r 2, r 3));
           eqR "multiplication" (r 6, R.* (r 2, r 3));
           eqR "division" (r 2, R./ (r 6, r 3));
           eqR "negation" (r ~2, R.~ (r 2));
           eqR "absolute value" (r 2, R.abs (r ~2));
           eqR "min" (r 2, R.min (r 2, r 3));
           eqR "max" (r 3, R.max (r 2, r 3));
           eqR "rem takes the sign of the dividend" (r 2, R.rem (r 5, r 3));
           eqR "rem with a negative dividend" (r ~2, R.rem (r ~5, r 3));
           eqR "multiply-add" (r 10, R.*+ (r 2, r 3, r 4));
           eqR "multiply-subtract" (r 2, R.*- (r 2, r 3, r 4)))),

        Case ("sign and comparison", fn () =>
          (A.eqInt "sign of a positive value" (1, R.sign (r 2));
           A.eqInt "sign of a negative value" (~1, R.sign (r ~2));
           A.eqInt "sign of zero" (0, R.sign (r 0));
           A.eqBool "signBit of a positive value" (false, R.signBit (r 2));
           A.eqBool "signBit of a negative value" (true, R.signBit (r ~2));
           A.eqBool "sameSign" (true, R.sameSign (r ~1, r ~2));
           eqR "copySign takes the second sign" (r ~2, R.copySign (r 2, r ~1));
           A.eqOrder "compare" (LESS, R.compare (r 1, r 2));
           A.eqBool "equality" (true, R.== (r 1, r 1));
           A.eqBool "inequality" (true, R.!= (r 1, r 2));
           A.eqBool "less" (true, R.< (r 1, r 2));
           A.eqBool "less or equal" (true, R.<= (r 1, r 1));
           A.eqBool "greater" (true, R.> (r 2, r 1));
           A.eqBool "greater or equal" (true, R.>= (r 1, r 1));
           A.eqBool "?= on equal values" (true, R.?= (r 1, r 1));
           A.eqBool "ordinary values are ordered"
             (false, R.unordered (r 1, r 2)))),

        Case ("classification", fn () =>
          (eqCls "one is normal" (IEEEReal.NORMAL, R.class (r 1));
           eqCls "zero" (IEEEReal.ZERO, R.class (r 0));
           A.eqBool "one is finite" (true, R.isFinite (r 1));
           A.eqBool "one is normal" (true, R.isNormal (r 1));
           A.eqBool "zero is not normal" (false, R.isNormal (r 0));
           A.eqBool "one is not a nan" (false, R.isNan (r 1)))),

        Case ("the IEEE special values",
          fn () =>
            if not ieee then ()
            else
              (eqCls "positive infinity" (IEEEReal.INF, R.class R.posInf);
               eqCls "negative infinity" (IEEEReal.INF, R.class R.negInf);
               eqCls "nan" (IEEEReal.NAN, R.class (nan ()));
               A.eqBool "a nan is not equal to itself"
                 (false, R.== (nan (), nan ()));
               A.eqBool "a nan is unordered" (true, R.unordered (nan (), r 1));
               A.eqBool "?= holds for a nan" (true, R.?= (nan (), r 1));
               A.raises "compare on a nan" A.isUnordered
                 (fn () => R.compare (nan (), r 1));
               A.that "compareReal reports UNORDERED"
                 (R.compareReal (nan (), r 1) = IEEEReal.UNORDERED);
               A.eqBool "signBit of a negative zero"
                 (true, R.signBit (negZero ()));
               eqR "min prefers the number over a nan" (r 1, R.min (r 1, nan ()));
               eqR "max prefers the number over a nan" (r 1, R.max (r 1, nan ()));
               A.raises "checkFloat of an infinity" A.isOverflow
                 (fn () => R.checkFloat R.posInf);
               A.raises "checkFloat of a nan" A.isDiv
                 (fn () => R.checkFloat (nan ()));
               A.noRaise "checkFloat of a finite value"
                 (fn () => R.checkFloat (r 1));
               A.that "nextAfter steps upwards"
                 (R.> (R.nextAfter (r 1, r 2), r 1));
               A.that "nextAfter steps downwards"
                 (R.< (R.nextAfter (r 1, r 0), r 1)))),

        Case ("rounding to integers", fn () =>
          (A.eqInt "floor rounds down" (1, R.floor (R./ (r 7, r 4)));
           A.eqInt "floor of a negative value" (~2, R.floor (R./ (r ~7, r 4)));
           A.eqInt "ceil rounds up" (2, R.ceil (R./ (r 5, r 4)));
           A.eqInt "trunc rounds towards zero" (1, R.trunc (R./ (r 7, r 4)));
           A.eqInt "trunc of a negative value" (~1, R.trunc (R./ (r ~7, r 4)));
           A.eqInt "round goes to nearest" (2, R.round (R./ (r 7, r 4)));
           A.eqInt "round ties to even" (2, R.round (R./ (r 5, r 2)));
           eqR "realFloor" (r 1, R.realFloor (R./ (r 7, r 4)));
           eqR "realCeil" (r 2, R.realCeil (R./ (r 5, r 4)));
           eqR "realTrunc" (r 1, R.realTrunc (R./ (r 7, r 4)));
           eqR "realRound" (r 2, R.realRound (R./ (r 7, r 4))))),

        Case ("toInt with an explicit rounding mode", fn () =>
          (A.eqInt "to negative infinity"
             (1, R.toInt IEEEReal.TO_NEGINF (R./ (r 7, r 4)));
           A.eqInt "to positive infinity"
             (2, R.toInt IEEEReal.TO_POSINF (R./ (r 5, r 4)));
           A.eqInt "towards zero"
             (~1, R.toInt IEEEReal.TO_ZERO (R./ (r ~7, r 4)));
           A.eqInt "to nearest"
             (2, R.toInt IEEEReal.TO_NEAREST (R./ (r 7, r 4))))),

        Case ("decomposition", fn () =>
          let
            val { man, exp } = R.toManExp (r 8)
            val { whole, frac } = R.split (R./ (r 7, r 4))
          in
            A.that "the mantissa is in the half-open unit interval"
              (R.>= (R.abs man, R./ (r 1, r 2)) andalso R.< (R.abs man, r 1));
            eqR "fromManExp reassembles"
              (r 8, R.fromManExp { man = man, exp = exp });
            eqR "the whole part" (r 1, whole);
            eqR "the fractional part" (R./ (r 3, r 4), frac);
            eqR "realMod is the fractional part"
              (R./ (r 3, r 4), R.realMod (R./ (r 7, r 4)))
          end),

        Case ("conversion to and from integers", fn () =>
          (eqR "fromInt" (r 3, R.fromInt 3);
           eqR "fromLargeInt" (r 3, R.fromLargeInt (LargeInt.fromInt 3));
           A.eqBy (op =, LargeInt.toString) "toLargeInt"
             (LargeInt.fromInt 3, R.toLargeInt IEEEReal.TO_NEAREST (r 3)))),

        Case ("conversion through LargeReal", fn () =>
          eqR "toLarge then fromLarge is the identity"
            (R./ (r 3, r 2),
             R.fromLarge IEEEReal.TO_NEAREST (R.toLarge (R./ (r 3, r 2))))),

        Case ("conversion to and from text", fn () =>
          (A.that "toString produces something fromString accepts"
             (case R.fromString (R.toString (r 1)) of
                  NONE => false | SOME v => R.== (v, r 1));
           A.that "fromString reads a decimal"
             (case R.fromString "1.5" of
                  NONE => false | SOME v => R.== (v, R./ (r 3, r 2)));
           A.that "fromString reads an exponent"
             (case R.fromString "1e3" of
                  NONE => false | SOME v => R.== (v, r 1000));
           A.that "fromString rejects letters"
             (not (isSome (R.fromString "abc")));
           A.that "scan leaves the rest of the stream"
             (case R.scan Substring.getc (Substring.full "1.5 tail") of
                  NONE => false
                | SOME (v, rest) =>
                    R.== (v, R./ (r 3, r 2))
                    andalso Substring.string rest = " tail");
           A.eqString "fmt in fixed notation"
             ("1.50", R.fmt (StringCvt.FIX (SOME 2)) (R./ (r 3, r 2)));
           A.eqString "fmt in scientific notation"
             ("1.50E0", R.fmt (StringCvt.SCI (SOME 2)) (R./ (r 3, r 2)));
           A.raises "a negative digit count" A.isSize
             (fn () => R.fmt (StringCvt.FIX (SOME (A.hide ~1))) (r 1)))),

        Case ("decimal approximations", fn () =>
          let val d = R.toDecimal (R./ (r 3, r 2))
          in
            A.eqBool "sign" (false, #sign d);
            A.eqIntList "digits" ([1, 5], #digits d);
            A.eqInt "exponent" (1, #exp d);
            case R.fromDecimal d of
                NONE => A.fail "fromDecimal returned NONE"
              | SOME v => eqR "fromDecimal inverts toDecimal" (R./ (r 3, r 2), v)
          end),

        P.forAll ("addition commutes", pairR, showPair,
                  fn (a, b) =>
                    P.implies (R.isFinite (R.+ (a, b)), R.== (R.+ (a, b), R.+ (b, a)))),

        P.forAll ("adding zero changes nothing", genR, showR,
                  fn a => P.implies (R.isFinite a, R.== (R.+ (a, r 0), a))),

        P.forAll ("multiplying by one changes nothing", genR, showR,
                  fn a => P.implies (R.isFinite a, R.== (R.* (a, r 1), a))),

        P.forAll ("negation is an involution", genR, showR,
                  fn a => P.implies (R.isFinite a, R.== (R.~ (R.~ a), a))),

        P.forAll ("abs is non-negative", genR, showR,
                  fn a => P.implies (R.isFinite a, R.>= (R.abs a, r 0))),

        P.forAll ("sign agrees with comparison against zero", genR, showR,
                  fn a =>
                    P.implies (R.isFinite a,
                               case R.sign a of
                                   0 => R.== (a, r 0)
                                 | 1 => R.> (a, r 0)
                                 | ~1 => R.< (a, r 0)
                                 | _ => false)),

        P.forAll ("compare agrees with the operators", pairR, showPair,
                  fn (a, b) =>
                    case R.compare (a, b) of
                        LESS => R.< (a, b)
                      | EQUAL => R.== (a, b)
                      | GREATER => R.> (a, b)),

        P.forAll ("floor is below and within one of its argument",
                  genR, showR,
                  fn a =>
                    let val f = R.realFloor a
                    in R.<= (f, a) andalso R.< (a, R.+ (f, r 1)) end),

        P.forAll ("split reassembles its argument", genR, showR,
                  fn a =>
                    let val { whole, frac } = R.split a
                    in R.== (R.+ (whole, frac), a) end),

        P.forAll ("toManExp and fromManExp round trip", genR, showR,
                  fn a =>
                    P.implies (not (R.== (a, r 0)),
                               R.== (R.fromManExp (R.toManExp a), a))),

        P.forAll ("the exact format round trips through fromString",
                  genR, showR,
                  fn a =>
                    case R.fromString (R.fmt StringCvt.EXACT a) of
                        NONE => false | SOME v => R.== (a, v)),

        P.forAll ("fromDecimal inverts toDecimal", genR, showR,
                  fn a =>
                    case R.fromDecimal (R.toDecimal a) of
                        NONE => false | SOME v => R.== (a, v)),

        P.forAll ("LargeReal round trips", genR, showR,
                  fn a =>
                    R.== (a, R.fromLarge IEEEReal.TO_NEAREST (R.toLarge a))),

        P.forAll ("multiply-subtract is multiply-add with a negated addend",
                  G.triple (genR, genR, genR),
                  Show.triple (showR, showR, showR),
                  fn (a, b, c) =>
                    P.implies (R.isFinite (R.- (R.* (a, b), c)),
                               R.== (R.*- (a, b, c), R.*+ (a, b, R.~ c))))
      ])
  end
