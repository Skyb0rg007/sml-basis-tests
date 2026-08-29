(* Tests for Word and Word8.
 *
 * Word.wordSize is implementation-defined, so nothing here hard-codes a width.
 * Every boundary value is derived from wordSize at run time -- that is what
 * makes the same source meaningful on a 31-, 32-, 63- and 64-bit system.
 *)

functor WordTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val ws = Word.wordSize
    val allOnes = Word.notb 0w0
    val topBit = Word.<< (0w1, Word.fromInt (ws - 1))
    val shiftPastEnd = Word.fromInt ws

    (* Word.toInt overflows only when the word range sticks out past maxInt. *)
    val wordExceedsInt =
      case Int.precision of
          SOME p => ws >= p
        | NONE => false

    (* toIntX round-trips every int exactly when the signed word range covers
     * the int range. *)
    val intFitsInWord =
      case Int.precision of
          SOME p => ws >= p
        | NONE => false

    val nonZeroWord = G.filter (fn w => w <> 0w0) G.word
    val showW = Show.word
    val wordPair = G.pair (G.word, G.word)
    val showWPair = Show.pair (showW, showW)
    val shiftAmount = G.map Word.fromInt (G.int (0, ws + 2))
    val showShift = Show.pair (showW, showW)

    val scanDec = StringCvt.scanString (Word.scan StringCvt.DEC)
    val scanHex = StringCvt.scanString (Word.scan StringCvt.HEX)
    val scanBin = StringCvt.scanString (Word.scan StringCvt.BIN)
    val scanOct = StringCvt.scanString (Word.scan StringCvt.OCT)
    val eqWordOption = A.eqBy (op =, Show.option showW)

    (* --- Word8 helpers ------------------------------------------------ *)
    val w8 = Word8.fromInt
    fun showW8 w = "0wx" ^ Word8.toString w
    val eqW8 = A.eqBy (op =, showW8)

    val suite = Group ("Word",
      [ Group ("width",
        [ Case ("wordSize is positive", fn () =>
            A.that "wordSize > 0" (ws > 0)),

          Case ("the all-ones pattern has every bit set", fn () =>
            (A.eqWord "notb 0w0 shifted right is still all ones"
               (allOnes, Word.orb (allOnes, 0w0));
             A.eqWord "adding one wraps to zero" (0w0, allOnes + 0w1))),

          Case ("the top bit is where wordSize says it is", fn () =>
            (A.eqWord "top bit doubled wraps to zero" (0w0, topBit + topBit);
             A.that "the top bit is set in all ones"
               (Word.andb (allOnes, topBit) = topBit)))
        ]),

        Group ("arithmetic wraps rather than trapping",
        [ Case ("addition wraps", fn () =>
            A.eqWord "allOnes + 1" (0w0, allOnes + 0w1)),

          Case ("subtraction wraps", fn () =>
            A.eqWord "0 - 1" (allOnes, 0w0 - 0w1)),

          Case ("multiplication wraps", fn () =>
            A.eqWord "allOnes * allOnes" (0w1, allOnes * allOnes)),

          Case ("negation wraps", fn () =>
            (A.eqWord "~0w0" (0w0, Word.~ 0w0);
             A.eqWord "~0w1" (allOnes, Word.~ 0w1))),

          Case ("no operation raises Overflow", fn () =>
            (A.noRaise "addition" (fn () => allOnes + allOnes);
             A.noRaise "multiplication" (fn () => allOnes * allOnes);
             A.noRaise "negation" (fn () => Word.~ allOnes))),

          Case ("division by zero", fn () =>
            (A.raises "div" A.isDiv (fn () => Word.div (0w1, 0w0));
             A.raises "mod" A.isDiv (fn () => Word.mod (0w1, 0w0))))
        ]),

        Group ("bitwise operations",
        [ Case ("andb, orb, xorb", fn () =>
            (A.eqWord "andb" (0w8, Word.andb (0w12, 0w10));
             A.eqWord "orb" (0w14, Word.orb (0w12, 0w10));
             A.eqWord "xorb" (0w6, Word.xorb (0w12, 0w10)))),

          Case ("notb", fn () =>
            (A.eqWord "notb 0" (allOnes, Word.notb 0w0);
             A.eqWord "notb allOnes" (0w0, Word.notb allOnes))),

          Case ("left shift", fn () =>
            (A.eqWord "by one" (0w2, Word.<< (0w1, 0w1));
             A.eqWord "by zero" (0w1, Word.<< (0w1, 0w0)))),

          Case ("logical right shift", fn () =>
            (A.eqWord "by one" (0w1, Word.>> (0w2, 0w1));
             A.eqWord "of the top bit brings in a zero"
               (0w0, Word.>> (topBit, Word.fromInt ws)))),

          (* The Basis specifies the result for shift counts at or beyond the
           * word width, which is where C-derived implementations tend to leak
           * undefined behaviour. *)
          Case ("shifting by the full width or more", fn () =>
            (A.eqWord "<< by wordSize" (0w0, Word.<< (allOnes, shiftPastEnd));
             A.eqWord "<< beyond wordSize"
               (0w0, Word.<< (allOnes, Word.fromInt (ws + 5)));
             A.eqWord ">> by wordSize" (0w0, Word.>> (allOnes, shiftPastEnd));
             A.eqWord ">> beyond wordSize"
               (0w0, Word.>> (allOnes, Word.fromInt (ws + 5))))),

          Case ("arithmetic right shift replicates the top bit", fn () =>
            (A.eqWord "negative pattern stays all ones"
               (allOnes, Word.~>> (allOnes, shiftPastEnd));
             A.eqWord "positive pattern becomes zero"
               (0w0, Word.~>> (0w1, shiftPastEnd));
             A.eqWord "top bit propagates"
               (allOnes, Word.~>> (topBit, Word.fromInt (ws - 1)))))
        ]),

        Group ("comparison is unsigned",
        [ Case ("the top bit makes a word large, not negative", fn () =>
            (A.eqBool "allOnes > 0" (true, Word.> (allOnes, 0w0));
             A.eqBool "allOnes > 1" (true, Word.> (allOnes, 0w1));
             A.eqOrder "compare" (GREATER, Word.compare (allOnes, 0w1)))),

          Case ("min and max", fn () =>
            (A.eqWord "min" (0w1, Word.min (0w1, allOnes));
             A.eqWord "max" (allOnes, Word.max (0w1, allOnes))))
        ]),

        Group ("conversion to and from int",
        [ Case ("fromInt of a negative int wraps", fn () =>
            A.eqWord "fromInt ~1" (allOnes, Word.fromInt ~1)),

          Case ("toIntX sign-extends", fn () =>
            (A.eqInt "all ones is ~1" (~1, Word.toIntX allOnes);
             A.eqInt "zero" (0, Word.toIntX 0w0);
             A.eqInt "one" (1, Word.toIntX 0w1))),

          Case ("toInt does not sign-extend", fn () =>
            (A.eqInt "small value" (5, Word.toInt 0w5);
             A.eqInt "zero" (0, Word.toInt 0w0))),

          Case ("toInt reports values outside the int range",
            fn () =>
              if not wordExceedsInt then ()
              else A.raises "toInt allOnes" A.isOverflow
                     (fn () => Word.toInt allOnes))
        ]),

        Group ("conversion to and from text",
        [ Case ("toString is hexadecimal without a prefix", fn () =>
            (A.eqString "255" ("FF", Word.toString 0w255);
             A.eqString "zero" ("0", Word.toString 0w0))),

          Case ("fromString reads hexadecimal", fn () =>
            (eqWordOption "bare" (SOME 0w255, Word.fromString "FF");
             eqWordOption "lower case" (SOME 0w255, Word.fromString "ff");
             eqWordOption "with prefix" (SOME 0w255, Word.fromString "0xFF"))),

          Case ("fromString rejects non-numbers", fn () =>
            (eqWordOption "empty" (NONE, Word.fromString "");
             eqWordOption "letters" (NONE, Word.fromString "zz"))),

          Case ("fmt in each radix", fn () =>
            (A.eqString "binary" ("101", Word.fmt StringCvt.BIN 0w5);
             A.eqString "octal" ("17", Word.fmt StringCvt.OCT 0w15);
             A.eqString "decimal" ("255", Word.fmt StringCvt.DEC 0w255);
             A.eqString "hexadecimal" ("FF", Word.fmt StringCvt.HEX 0w255))),

          Case ("scan in each radix", fn () =>
            (eqWordOption "binary" (SOME 0w5, scanBin "101");
             eqWordOption "octal" (SOME 0w15, scanOct "17");
             eqWordOption "decimal" (SOME 0w255, scanDec "255");
             eqWordOption "hexadecimal" (SOME 0w255, scanHex "FF"))),

          (* Unlike the integer grammar, the word grammar has no sign at all,
           * but it does admit the 0w family of prefixes. *)
          Case ("scan does not accept a sign", fn () =>
            (eqWordOption "tilde" (NONE, scanDec "~1");
             eqWordOption "hyphen" (NONE, scanDec "-1");
             eqWordOption "plus" (NONE, scanDec "+1"))),

          Case ("scan accepts the 0w prefixes", fn () =>
            (eqWordOption "0w in decimal" (SOME 0w255, scanDec "0w255");
             eqWordOption "0w in binary" (SOME 0w5, scanBin "0w101");
             eqWordOption "0wx in hexadecimal" (SOME 0w255, scanHex "0wxFF");
             eqWordOption "0wX in hexadecimal" (SOME 0w255, scanHex "0wXFF");
             eqWordOption "fromString takes 0wx"
               (SOME 0w255, Word.fromString "0wxFF")))
        ]),

        Group ("Word8",
        [ Case ("wordSize is eight", fn () =>
            A.eqInt "Word8.wordSize" (8, Word8.wordSize)),

          Case ("values wrap at 256", fn () =>
            (eqW8 "fromInt 256" (w8 0, w8 256);
             eqW8 "fromInt 300" (w8 44, w8 300);
             eqW8 "fromInt ~1" (w8 255, w8 ~1);
             eqW8 "255 + 1" (w8 0, Word8.+ (w8 255, w8 1)))),

          Case ("notb covers eight bits", fn () =>
            eqW8 "notb 0" (w8 255, Word8.notb (w8 0))),

          Case ("toInt is unsigned and toIntX is signed", fn () =>
            (A.eqInt "toInt 255" (255, Word8.toInt (w8 255));
             A.eqInt "toIntX 255" (~1, Word8.toIntX (w8 255));
             A.eqInt "toIntX 127" (127, Word8.toIntX (w8 127));
             A.eqInt "toIntX 128" (~128, Word8.toIntX (w8 128)))),

          Case ("shifting past the width", fn () =>
            (eqW8 "<< by 8" (w8 0, Word8.<< (w8 255, 0w8));
             eqW8 ">> by 8" (w8 0, Word8.>> (w8 255, 0w8));
             eqW8 "~>> by 8 of a negative pattern"
               (w8 255, Word8.~>> (w8 255, 0w8)))),

          Case ("toString and fromString", fn () =>
            (A.eqString "toString" ("FF", Word8.toString (w8 255));
             A.eqBy (op =, Show.option showW8) "fromString"
               (SOME (w8 255), Word8.fromString "FF")))
        ]),

        Group ("laws",
        [ P.forAll ("addition commutes", wordPair, showWPair,
                    fn (a, b) => a + b = b + a),

          P.forAll ("multiplication commutes", wordPair, showWPair,
                    fn (a, b) => a * b = b * a),

          P.forAll ("subtraction inverts addition", wordPair, showWPair,
                    fn (a, b) => (a + b) - b = a),

          P.forAll ("a word minus itself is zero", G.word, showW,
                    fn a => a - a = 0w0),

          P.forAll ("notb is an involution", G.word, showW,
                    fn a => Word.notb (Word.notb a) = a),

          P.forAll ("xorb with itself annihilates", G.word, showW,
                    fn a => Word.xorb (a, a) = 0w0),

          P.forAll ("a word and its complement share no bits", G.word, showW,
                    fn a => Word.andb (a, Word.notb a) = 0w0),

          P.forAll ("a word or its complement is all ones", G.word, showW,
                    fn a => Word.orb (a, Word.notb a) = allOnes),

          P.forAll ("andb and orb are idempotent", G.word, showW,
                    fn a => Word.andb (a, a) = a andalso Word.orb (a, a) = a),

          P.forAll ("de Morgan for words", wordPair, showWPair,
                    fn (a, b) =>
                      Word.notb (Word.andb (a, b))
                      = Word.orb (Word.notb a, Word.notb b)),

          P.forAll ("xorb is addition without carry", wordPair, showWPair,
                    fn (a, b) =>
                      Word.xorb (a, b)
                      = Word.andb (Word.orb (a, b), Word.notb (Word.andb (a, b)))),

          P.forAll ("shifting left then right clears the high bits",
                    G.pair (G.word, shiftAmount), showShift,
                    fn (a, k) =>
                      Word.>> (Word.<< (a, k), k)
                      = Word.andb (a, Word.>> (allOnes, k))),

          P.forAll ("a left shift is a multiplication by a power of two",
                    G.pair (G.word, G.map Word.fromInt (G.int (0, ws - 1))),
                    showShift,
                    fn (a, k) => Word.<< (a, k) = a * Word.<< (0w1, k)),

          P.forAll ("shifting by the width or beyond yields zero",
                    G.pair (G.word, G.map Word.fromInt (G.int (ws, ws + 8))),
                    showShift,
                    fn (a, k) =>
                      Word.<< (a, k) = 0w0 andalso Word.>> (a, k) = 0w0),

          P.forAll ("div and mod reconstruct the dividend",
                    G.pair (G.word, nonZeroWord), showWPair,
                    fn (a, b) => Word.div (a, b) * b + Word.mod (a, b) = a),

          P.forAll ("mod is smaller than the divisor",
                    G.pair (G.word, nonZeroWord), showWPair,
                    fn (a, b) => Word.< (Word.mod (a, b), b)),

          P.forAll ("compare agrees with the operators", wordPair, showWPair,
                    fn (a, b) =>
                      case Word.compare (a, b) of
                          LESS => Word.< (a, b)
                        | EQUAL => a = b
                        | GREATER => Word.> (a, b)),

          P.forAll ("fromString inverts toString", G.word, showW,
                    fn a => Word.fromString (Word.toString a) = SOME a),

          P.forAll ("scan inverts fmt in every radix", G.word, showW,
                    fn a =>
                      List.all
                        (fn (radix, scan) => scan (Word.fmt radix a) = SOME a)
                        [ (StringCvt.BIN, scanBin),
                          (StringCvt.OCT, scanOct),
                          (StringCvt.DEC, scanDec),
                          (StringCvt.HEX, scanHex) ]),

          P.forAll ("fromInt inverts toIntX", G.word, showW,
                    fn a => Word.fromInt (Word.toIntX a) = a),

          P.forAll ("toIntX inverts fromInt when the ranges allow",
                    G.anyInt, Show.int,
                    fn n =>
                      P.implies (intFitsInWord,
                                 Word.toIntX (Word.fromInt n) = n))
        ])
      ])
  end
