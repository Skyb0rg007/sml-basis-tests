(* Tests for the Char structure.
 *
 * The Basis pins down the classification predicates only over the ASCII
 * range; above 127 the answers are locale- or implementation-defined.  The
 * ASCII laws are therefore tested against an ASCII generator, and the
 * behaviour above 127 is asserted only when the configuration declares that
 * the predicates are ASCII-only.
 *)

functor CharTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val maxOrd = Char.maxOrd
    val hasHighChars = maxOrd > 127
    val highChar = G.map Char.chr (G.int (128, if hasHighChars then maxOrd else 128))

    val eqCharOpt = A.eqBy (op =, Show.option Show.char)

    val suite = Group ("Char",
      [ Group ("the character set",
        [ Case ("maxOrd is at least 255", fn () =>
            A.that ("maxOrd = " ^ Int.toString maxOrd) (maxOrd >= 255)),

          Case ("minChar and maxChar sit at the ends", fn () =>
            (A.eqInt "ord minChar" (0, Char.ord Char.minChar);
             A.eqInt "ord maxChar" (maxOrd, Char.ord Char.maxChar))),

          Case ("chr and ord invert each other", fn () =>
            (A.eqInt "ord of chr 65" (65, Char.ord (Char.chr 65));
             A.eqChar "chr of ord A" (#"A", Char.chr (Char.ord #"A")))),

          Case ("chr rejects codes outside the range", fn () =>
            (A.raises "negative" A.isChr (fn () => Char.chr ~1);
             A.raises "past maxOrd" A.isChr (fn () => Char.chr (maxOrd + A.hide 1)))),

          Case ("succ and pred", fn () =>
            (A.eqChar "succ" (#"B", Char.succ #"A");
             A.eqChar "pred" (#"A", Char.pred #"B");
             A.raises "succ of the last character" A.isChr
               (fn () => Char.succ Char.maxChar);
             A.raises "pred of the first character" A.isChr
               (fn () => Char.pred Char.minChar)))
        ]),

        Group ("classification over ASCII",
        [ Case ("isAscii", fn () =>
            (A.eqBool "letter" (true, Char.isAscii #"A");
             A.eqBool "code 127" (true, Char.isAscii (Char.chr 127));
             if hasHighChars
             then A.eqBool "code 128" (false, Char.isAscii (Char.chr 128))
             else ())),

          Case ("isDigit", fn () =>
            (A.eqBool "0" (true, Char.isDigit #"0");
             A.eqBool "9" (true, Char.isDigit #"9");
             A.eqBool "a" (false, Char.isDigit #"a");
             A.eqBool "slash" (false, Char.isDigit #"/"))),

          Case ("isHexDigit", fn () =>
            (A.eqBool "9" (true, Char.isHexDigit #"9");
             A.eqBool "f" (true, Char.isHexDigit #"f");
             A.eqBool "F" (true, Char.isHexDigit #"F");
             A.eqBool "g" (false, Char.isHexDigit #"g"))),

          Case ("isAlpha, isUpper, isLower", fn () =>
            (A.eqBool "A is alpha" (true, Char.isAlpha #"A");
             A.eqBool "z is alpha" (true, Char.isAlpha #"z");
             A.eqBool "0 is not alpha" (false, Char.isAlpha #"0");
             A.eqBool "A is upper" (true, Char.isUpper #"A");
             A.eqBool "a is not upper" (false, Char.isUpper #"a");
             A.eqBool "a is lower" (true, Char.isLower #"a");
             A.eqBool "A is not lower" (false, Char.isLower #"A"))),

          Case ("isAlphaNum", fn () =>
            (A.eqBool "letter" (true, Char.isAlphaNum #"a");
             A.eqBool "digit" (true, Char.isAlphaNum #"7");
             A.eqBool "punctuation" (false, Char.isAlphaNum #"!"))),

          Case ("isSpace covers the six ASCII whitespace codes", fn () =>
            (A.eqBool "space" (true, Char.isSpace #" ");
             A.eqBool "tab" (true, Char.isSpace #"\t");
             A.eqBool "newline" (true, Char.isSpace #"\n");
             A.eqBool "vertical tab" (true, Char.isSpace (Char.chr 11));
             A.eqBool "form feed" (true, Char.isSpace #"\f");
             A.eqBool "carriage return" (true, Char.isSpace #"\r");
             A.eqBool "letter" (false, Char.isSpace #"a");
             A.eqBool "nul" (false, Char.isSpace (Char.chr 0)))),

          Case ("isPunct, isGraph, isPrint, isCntrl", fn () =>
            (A.eqBool "bang is punctuation" (true, Char.isPunct #"!");
             A.eqBool "letter is not punctuation" (false, Char.isPunct #"a");
             A.eqBool "space is not graphic" (false, Char.isGraph #" ");
             A.eqBool "bang is graphic" (true, Char.isGraph #"!");
             A.eqBool "space is printable" (true, Char.isPrint #" ");
             A.eqBool "newline is not printable" (false, Char.isPrint #"\n");
             A.eqBool "nul is a control character" (true, Char.isCntrl (Char.chr 0));
             A.eqBool "code 127 is a control character"
               (true, Char.isCntrl (Char.chr 127));
             A.eqBool "letter is not a control character"
               (false, Char.isCntrl #"a"))),

          Case ("toUpper and toLower", fn () =>
            (A.eqChar "lower to upper" (#"A", Char.toUpper #"a");
             A.eqChar "upper stays upper" (#"A", Char.toUpper #"A");
             A.eqChar "upper to lower" (#"a", Char.toLower #"A");
             A.eqChar "lower stays lower" (#"a", Char.toLower #"a");
             A.eqChar "digits are unchanged" (#"7", Char.toUpper #"7");
             A.eqChar "punctuation is unchanged" (#"!", Char.toLower #"!")))
        ]),

        Group ("classification above ASCII",
          onlyIf (hasHighChars andalso C.charPredicatesAreAscii,
                  if hasHighChars
                  then "implementation not declared ASCII-only above 127"
                  else "the character set stops at 127")
          [ Case ("no character above 127 is classified as ASCII text",
              fn () =>
                let
                  fun check i =
                    let val c = Char.chr i
                    in
                      A.eqBool ("isAlpha of code " ^ Int.toString i)
                        (false, Char.isAlpha c);
                      A.eqBool ("isDigit of code " ^ Int.toString i)
                        (false, Char.isDigit c);
                      A.eqBool ("isSpace of code " ^ Int.toString i)
                        (false, Char.isSpace c);
                      A.eqBool ("isAscii of code " ^ Int.toString i)
                        (false, Char.isAscii c);
                      A.eqBool ("isUpper of code " ^ Int.toString i)
                        (false, Char.isUpper c);
                      A.eqBool ("isLower of code " ^ Int.toString i)
                        (false, Char.isLower c)
                    end
                  fun loop i = if i > maxOrd then () else (check i; loop (i + 1))
                in
                  loop 128
                end),

            Case ("case conversion above 127 is the identity", fn () =>
              let
                fun loop i =
                  if i > maxOrd then ()
                  else
                    let val c = Char.chr i
                    in
                      A.eqChar ("toUpper of code " ^ Int.toString i)
                        (c, Char.toUpper c);
                      A.eqChar ("toLower of code " ^ Int.toString i)
                        (c, Char.toLower c);
                      loop (i + 1)
                    end
              in
                loop 128
              end)
          ]),

        Group ("membership and ordering",
        [ Case ("contains and notContains", fn () =>
            (A.eqBool "present" (true, Char.contains "abc" #"b");
             A.eqBool "absent" (false, Char.contains "abc" #"z");
             A.eqBool "empty string" (false, Char.contains "" #"a");
             A.eqBool "notContains is the negation"
               (true, Char.notContains "abc" #"z"))),

          Case ("comparison follows the ordinals", fn () =>
            (A.eqBool "a < b" (true, Char.< (#"a", #"b"));
             A.eqBool "A < a" (true, Char.< (#"A", #"a"));
             A.eqOrder "compare" (LESS, Char.compare (#"a", #"b"));
             A.eqOrder "compare equal" (EQUAL, Char.compare (#"a", #"a"))))
        ]),

        Group ("conversion to and from text",
        [ Case ("toString leaves printable characters alone", fn () =>
            (A.eqString "letter" ("a", Char.toString #"a");
             A.eqString "space" (" ", Char.toString #" "))),

          Case ("toString escapes what SML syntax requires", fn () =>
            (A.eqString "newline" ("\\n", Char.toString #"\n");
             A.eqString "tab" ("\\t", Char.toString #"\t");
             A.eqString "backslash" ("\\\\", Char.toString #"\\");
             A.eqString "double quote" ("\\\"", Char.toString #"\""))),

          Case ("fromString reads the escapes back", fn () =>
            (eqCharOpt "letter" (SOME #"a", Char.fromString "a");
             eqCharOpt "newline" (SOME #"\n", Char.fromString "\\n");
             eqCharOpt "tab" (SOME #"\t", Char.fromString "\\t");
             eqCharOpt "backslash" (SOME #"\\", Char.fromString "\\\\");
             eqCharOpt "decimal escape" (SOME #"A", Char.fromString "\\065"))),

          Case ("fromString rejects malformed input", fn () =>
            (eqCharOpt "empty" (NONE, Char.fromString "");
             eqCharOpt "lone backslash" (NONE, Char.fromString "\\");
             eqCharOpt "unknown escape" (NONE, Char.fromString "\\q"))),

          Case ("toCString uses C escapes", fn () =>
            (A.eqString "newline" ("\\n", Char.toCString #"\n");
             A.eqString "backslash" ("\\\\", Char.toCString #"\\");
             A.eqString "letter" ("a", Char.toCString #"a"))),

          Case ("fromCString reads C escapes", fn () =>
            (eqCharOpt "newline" (SOME #"\n", Char.fromCString "\\n");
             eqCharOpt "octal escape" (SOME #"A", Char.fromCString "\\101");
             eqCharOpt "letter" (SOME #"a", Char.fromCString "a")))
        ]),

        Group ("laws",
        [ P.forAll ("ord inverts chr", G.int (0, maxOrd), Show.int,
                    fn i => Char.ord (Char.chr i) = i),

          P.forAll ("chr inverts ord", G.char, Show.char,
                    fn c => Char.chr (Char.ord c) = c),

          P.forAll ("ord lands inside the character set", G.char, Show.char,
                    fn c => Char.ord c >= 0 andalso Char.ord c <= maxOrd),

          P.forAll ("comparison is comparison of ordinals",
                    G.pair (G.char, G.char), Show.pair (Show.char, Show.char),
                    fn (a, b) =>
                      Char.< (a, b) = (Char.ord a < Char.ord b)
                      andalso Char.<= (a, b) = (Char.ord a <= Char.ord b)
                      andalso Char.compare (a, b) = Int.compare (Char.ord a, Char.ord b)),

          P.forAll ("alphanumeric splits into alphabetic and numeric",
                    G.asciiChar, Show.char,
                    fn c => Char.isAlphaNum c = (Char.isAlpha c orelse Char.isDigit c)),

          P.forAll ("alphabetic splits into upper and lower case",
                    G.asciiChar, Show.char,
                    fn c => Char.isAlpha c = (Char.isUpper c orelse Char.isLower c)),

          P.forAll ("no character is both upper and lower case",
                    G.asciiChar, Show.char,
                    fn c => not (Char.isUpper c andalso Char.isLower c)),

          P.forAll ("printable is graphic or a space",
                    G.asciiChar, Show.char,
                    fn c => Char.isPrint c = (Char.isGraph c orelse c = #" ")),

          P.forAll ("graphic is printable but not whitespace",
                    G.asciiChar, Show.char,
                    fn c => Char.isGraph c = (Char.isPrint c andalso not (Char.isSpace c))),

          P.forAll ("control is the complement of printable, over ASCII",
                    G.asciiChar, Show.char,
                    fn c => Char.isCntrl c = not (Char.isPrint c)),

          P.forAll ("graphic characters are alphanumeric or punctuation",
                    G.asciiChar, Show.char,
                    fn c => Char.isGraph c = (Char.isAlphaNum c orelse Char.isPunct c)),

          P.forAll ("digits are hexadecimal digits", G.asciiChar, Show.char,
                    fn c => P.implies (Char.isDigit c, Char.isHexDigit c)),

          P.forAll ("toUpper is idempotent", G.char, Show.char,
                    fn c => Char.toUpper (Char.toUpper c) = Char.toUpper c),

          P.forAll ("toLower is idempotent", G.char, Show.char,
                    fn c => Char.toLower (Char.toLower c) = Char.toLower c),

          P.forAll ("case conversion round trips for ASCII letters",
                    G.asciiChar, Show.char,
                    fn c =>
                      P.implies (Char.isLower c,
                                 Char.toLower (Char.toUpper c) = c)
                      andalso P.implies (Char.isUpper c,
                                         Char.toUpper (Char.toLower c) = c)),

          P.forAll ("toUpper only changes lower case letters",
                    G.asciiChar, Show.char,
                    fn c => P.implies (not (Char.isLower c), Char.toUpper c = c)),

          P.forAll ("toLower only changes upper case letters",
                    G.asciiChar, Show.char,
                    fn c => P.implies (not (Char.isUpper c), Char.toLower c = c)),

          P.forAll ("contains agrees with membership in the explosion",
                    G.pair (G.asciiString, G.asciiChar),
                    Show.pair (Show.string, Show.char),
                    fn (s, c) =>
                      Char.contains s c = List.exists (fn x => x = c) (String.explode s)),

          P.forAll ("notContains is the negation of contains",
                    G.pair (G.asciiString, G.asciiChar),
                    Show.pair (Show.string, Show.char),
                    fn (s, c) => Char.notContains s c = not (Char.contains s c)),

          P.forAll ("fromString inverts toString", G.char, Show.char,
                    fn c => Char.fromString (Char.toString c) = SOME c),

          P.forAll ("fromCString inverts toCString", G.char, Show.char,
                    fn c => Char.fromCString (Char.toCString c) = SOME c),

          P.forAll ("succ and pred are inverse in the interior",
                    G.map Char.chr (G.int (1, maxOrd - 1)), Show.char,
                    fn c => Char.pred (Char.succ c) = c
                            andalso Char.succ (Char.pred c) = c)
        ])
      ])
  end
