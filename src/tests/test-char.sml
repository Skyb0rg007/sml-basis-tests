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

    (* The specification writes toString and toCString out as a table; these
     * are that table, so that the properties below can check every character
     * rather than the handful a unit test can name. *)
    fun controlEscape i =
      if i = 7 then SOME "\\a"
      else if i = 8 then SOME "\\b"
      else if i = 9 then SOME "\\t"
      else if i = 10 then SOME "\\n"
      else if i = 11 then SOME "\\v"
      else if i = 12 then SOME "\\f"
      else if i = 13 then SOME "\\r"
      else NONE

    fun specToString c =
      let
        val i = Char.ord c
      in
        if c = #"\\" then "\\\\"
        else if c = #"\"" then "\\\""
        else case controlEscape i of
                 SOME e => e
               | NONE =>
                   if i < 32 then "\\^" ^ String.str (Char.chr (i + 64))
                   else if i <= 126 then String.str c
                   else if i < 1000 then
                     "\\" ^ StringCvt.padLeft #"0" 3 (Int.toString i)
                   else
                     "\\u" ^ StringCvt.padLeft #"0" 4
                               (Int.fmt StringCvt.HEX i)
      end

    fun specToCString c =
      let
        val i = Char.ord c
      in
        if c = #"\\" then "\\\\"
        else if c = #"\"" then "\\\""
        else if c = #"?" then "\\?"
        else if c = #"'" then "\\'"
        else case controlEscape i of
                 SOME e => e
               | NONE =>
                   if i >= 32 andalso i <= 126 then String.str c
                   else "\\" ^ StringCvt.padLeft #"0" 3
                                 (Int.fmt StringCvt.OCT i)
      end

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

          (* Char.scan reads one character in SML source syntax, so unlike the
           * numeric scanners it does not skip leading whitespace: a space is
           * itself a character literal. *)
          Case ("scan reads one character and stops", fn () =>
            (case Char.scan Substring.getc (Substring.full "abc") of
                 NONE => A.fail "scan returned NONE"
               | SOME (c, rest) =>
                   (A.eqChar "the character" (#"a", c);
                    A.eqString "the remainder" ("bc", Substring.string rest));
             case Char.scan Substring.getc (Substring.full "\\nrest") of
                 NONE => A.fail "scan of an escape returned NONE"
               | SOME (c, rest) =>
                   (A.eqChar "the escape" (#"\n", c);
                    A.eqString "the remainder" ("rest", Substring.string rest)))),

          Case ("scan rejects what is not a character", fn () =>
            A.that "an empty source"
              (not (isSome (Char.scan Substring.getc (Substring.full ""))))),

          (* "The common control characters are converted to two-character
           * escape sequences" -- the whole table, not a sample of it. *)
          Case ("toString converts every named control character", fn () =>
            (A.eqString "alert" ("\\a", Char.toString (Char.chr 7));
             A.eqString "backspace" ("\\b", Char.toString (Char.chr 8));
             A.eqString "tab" ("\\t", Char.toString (Char.chr 9));
             A.eqString "newline" ("\\n", Char.toString (Char.chr 10));
             A.eqString "vertical tab" ("\\v", Char.toString (Char.chr 11));
             A.eqString "form feed" ("\\f", Char.toString (Char.chr 12));
             A.eqString "carriage return" ("\\r", Char.toString (Char.chr 13)))),

          (* "The remaining characters whose codes are less than 32 are
           * represented by three-character strings in control character
           * notation, e.g., #"\000" maps to "\^@", #"\001" maps to "\^A"." *)
          Case ("toString uses control notation below 32", fn () =>
            (A.eqString "nul" ("\\^@", Char.toString (Char.chr 0));
             A.eqString "code 1" ("\\^A", Char.toString (Char.chr 1));
             A.eqString "code 26" ("\\^Z", Char.toString (Char.chr 26));
             A.eqString "code 31" ("\\^_", Char.toString (Char.chr 31)))),

          (* "All other characters (i.e., those whose codes are greater than
           * 126 but less than 1000) are mapped to four-character strings of
           * the form "\ddd"." *)
          Case ("toString uses three decimal digits above 126", fn () =>
            (A.eqString "delete" ("\\127", Char.toString (Char.chr 127));
             A.eqString "code 128" ("\\128", Char.toString (Char.chr 128));
             A.eqString "code 255" ("\\255", Char.toString (Char.chr 255)))),

          (* The samples the specification tabulates for fromString. *)
          Case ("the sample conversions from the specification", fn () =>
            (eqCharOpt "a backslash and a letter" (NONE, Char.fromString "\\q");
             eqCharOpt "a letter then a control character"
               (SOME #"a", Char.fromString "a\^D");
             eqCharOpt "a letter then an escaped formatting sequence"
               (SOME #"a", Char.fromString "a\\ \\\\q");
             eqCharOpt "an escaped formatting sequence alone"
               (NONE, Char.fromString "\\ \\");
             eqCharOpt "the empty string" (NONE, Char.fromString "");
             eqCharOpt "a formatting sequence then a control character"
               (NONE, Char.fromString "\\ \\\^D");
             eqCharOpt "an unterminated formatting sequence"
               (NONE, Char.fromString "\\ a"))),

          Case ("fromString reads every escape the grammar allows", fn () =>
            (eqCharOpt "alert" (SOME (Char.chr 7), Char.fromString "\\a");
             eqCharOpt "backspace" (SOME (Char.chr 8), Char.fromString "\\b");
             eqCharOpt "vertical tab" (SOME (Char.chr 11), Char.fromString "\\v");
             eqCharOpt "form feed" (SOME (Char.chr 12), Char.fromString "\\f");
             eqCharOpt "carriage return" (SOME (Char.chr 13), Char.fromString "\\r");
             eqCharOpt "double quote" (SOME #"\"", Char.fromString "\\\"");
             eqCharOpt "control escape at the bottom of the range"
               (SOME (Char.chr 0), Char.fromString "\\^@");
             eqCharOpt "control escape" (SOME (Char.chr 8), Char.fromString "\\^H");
             eqCharOpt "control escape at the top of the range"
               (SOME (Char.chr 31), Char.fromString "\\^_");
             eqCharOpt "decimal escape" (SOME (Char.chr 255), Char.fromString "\\255");
             eqCharOpt "hexadecimal escape"
               (SOME #"A", Char.fromString "\\u0041"))),

          (* "In the escape sequences involving decimal or hexadecimal digits,
           * if the resulting value cannot be represented in the character
           * set, NONE is returned." *)
          Case ("fromString rejects an escape outside the character set",
            fn () =>
              if maxOrd >= 999 then ()
              else
                (eqCharOpt "decimal 999" (NONE, Char.fromString "\\999");
                 eqCharOpt "hexadecimal FFFF" (NONE, Char.fromString "\\uFFFF"))),

          Case ("fromString rejects a non-printable first character", fn () =>
            (eqCharOpt "a control character"
               (NONE, Char.fromString (String.str (Char.chr 4)));
             eqCharOpt "a newline"
               (NONE, Char.fromString "\n"))),

          Case ("fromString rejects a malformed control escape", fn () =>
            (eqCharOpt "below the range" (NONE, Char.fromString "\\^?");
             eqCharOpt "above the range" (NONE, Char.fromString "\\^a");
             eqCharOpt "too few decimal digits" (NONE, Char.fromString "\\12");
             eqCharOpt "too few hexadecimal digits"
               (NONE, Char.fromString "\\u41"))),

          (* "escaped formatting sequences (\f...f\) are passed over during
           * scanning.  Such sequences are successfully scanned, so that the
           * remaining stream returned by scan will never have a valid escaped
           * formatting sequence as its prefix." *)
          Case ("scan passes over an escaped formatting sequence", fn () =>
            (case Char.scan Substring.getc (Substring.full "\\ \\ab") of
                 NONE => A.fail "a leading formatting sequence stopped the scan"
               | SOME (c, rest) =>
                   (A.eqChar "the character after it" (#"a", c);
                    A.eqString "the remainder" ("b", Substring.string rest));
             case Char.scan Substring.getc (Substring.full "a\\ \\b") of
                 NONE => A.fail "scan returned NONE"
               | SOME (c, rest) =>
                   (A.eqChar "the character" (#"a", c);
                    A.eqString "the remainder has no formatting escape left"
                      ("b", Substring.string rest));
             case Char.scan Substring.getc
                            (Substring.full "\\\n\t \\Z") of
                 NONE => A.fail "a multi-character formatting sequence stopped the scan"
               | SOME (c, rest) =>
                   (A.eqChar "the character after it" (#"Z", c);
                    A.eqString "the remainder" ("", Substring.string rest)))),

          Case ("toCString uses C escapes", fn () =>
            (A.eqString "newline" ("\\n", Char.toCString #"\n");
             A.eqString "backslash" ("\\\\", Char.toCString #"\\");
             A.eqString "letter" ("a", Char.toCString #"a"))),

          Case ("fromCString reads C escapes", fn () =>
            (eqCharOpt "newline" (SOME #"\n", Char.fromCString "\\n");
             eqCharOpt "octal escape" (SOME #"A", Char.fromCString "\\101");
             eqCharOpt "letter" (SOME #"a", Char.fromCString "a"))),

          (* "printable characters, except for #"\\", #"\"", #"?", and #"'"
           * are left unchanged", and everything else that is not one of the
           * named control characters becomes three octal digits. *)
          Case ("toCString escapes the four C-specific characters", fn () =>
            (A.eqString "question mark" ("\\?", Char.toCString #"?");
             A.eqString "single quote" ("\\'", Char.toCString #"'");
             A.eqString "double quote" ("\\\"", Char.toCString #"\"");
             A.eqString "backslash" ("\\\\", Char.toCString #"\\"))),

          Case ("toCString uses three octal digits elsewhere", fn () =>
            (A.eqString "nul" ("\\000", Char.toCString (Char.chr 0));
             A.eqString "code 1" ("\\001", Char.toCString (Char.chr 1));
             A.eqString "escape" ("\\033", Char.toCString (Char.chr 27));
             A.eqString "delete" ("\\177", Char.toCString (Char.chr 127));
             A.eqString "code 255" ("\\377", Char.toCString (Char.chr 255)))),

          Case ("toCString converts every named control character", fn () =>
            (A.eqString "alert" ("\\a", Char.toCString (Char.chr 7));
             A.eqString "backspace" ("\\b", Char.toCString (Char.chr 8));
             A.eqString "tab" ("\\t", Char.toCString (Char.chr 9));
             A.eqString "newline" ("\\n", Char.toCString (Char.chr 10));
             A.eqString "vertical tab" ("\\v", Char.toCString (Char.chr 11));
             A.eqString "form feed" ("\\f", Char.toCString (Char.chr 12));
             A.eqString "carriage return" ("\\r", Char.toCString (Char.chr 13)))),

          Case ("fromCString reads the C escape table", fn () =>
            (eqCharOpt "alert" (SOME (Char.chr 7), Char.fromCString "\\a");
             eqCharOpt "backspace" (SOME (Char.chr 8), Char.fromCString "\\b");
             eqCharOpt "tab" (SOME (Char.chr 9), Char.fromCString "\\t");
             eqCharOpt "vertical tab" (SOME (Char.chr 11), Char.fromCString "\\v");
             eqCharOpt "form feed" (SOME (Char.chr 12), Char.fromCString "\\f");
             eqCharOpt "carriage return" (SOME (Char.chr 13), Char.fromCString "\\r");
             eqCharOpt "question mark" (SOME #"?", Char.fromCString "\\?");
             eqCharOpt "single quote" (SOME #"'", Char.fromCString "\\'");
             eqCharOpt "double quote" (SOME #"\"", Char.fromCString "\\\"");
             eqCharOpt "backslash" (SOME #"\\", Char.fromCString "\\\\");
             eqCharOpt "control escape" (SOME (Char.chr 8), Char.fromCString "\\^H"))),

          (* "\ooo consists of one to three octal digits" and "\xhh, where hh
           * is a sequence of hexadecimal digits", with "the sequence of
           * digits ... taken to be the longest sequence of such
           * characters". *)
          Case ("fromCString reads octal and hexadecimal escapes", fn () =>
            (eqCharOpt "one octal digit" (SOME (Char.chr 1), Char.fromCString "\\1");
             eqCharOpt "two octal digits" (SOME (Char.chr 10), Char.fromCString "\\12");
             eqCharOpt "three octal digits"
               (SOME (Char.chr 255), Char.fromCString "\\377");
             eqCharOpt "the longest octal run wins"
               (SOME (Char.chr 8), Char.fromCString "\\10");
             eqCharOpt "hexadecimal" (SOME #"A", Char.fromCString "\\x41");
             eqCharOpt "lower-case hexadecimal"
               (SOME (Char.chr 255), Char.fromCString "\\xff"))),

          Case ("fromCString rejects what C does not allow", fn () =>
            (eqCharOpt "an unknown escape" (NONE, Char.fromCString "\\q");
             eqCharOpt "the empty string" (NONE, Char.fromCString "");
             eqCharOpt "a non-printable character"
               (NONE, Char.fromCString (String.str (Char.chr 4))))),

          (* "Note that fromCString accepts an unescaped single quote
           * character, but does not accept an unescaped double quote
           * character." *)
          Case ("fromCString accepts a bare quote only in the single case",
            fn () =>
              (eqCharOpt "single quote" (SOME #"'", Char.fromCString "'");
               eqCharOpt "double quote" (NONE, Char.fromCString "\"")))
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

          (* The Discussion fixes each predicate as a range test on the
           * character code; Char is locale-independent, so this is the
           * definition and not merely a consequence of one. *)
          P.forAll ("the predicates have the definitions the Discussion gives",
                    G.asciiChar, Show.char,
                    fn c =>
                      Char.isUpper c = (#"A" <= c andalso c <= #"Z")
                      andalso Char.isLower c = (#"a" <= c andalso c <= #"z")
                      andalso Char.isDigit c = (#"0" <= c andalso c <= #"9")
                      andalso Char.isAlpha c = (Char.isUpper c orelse Char.isLower c)
                      andalso Char.isAlphaNum c
                              = (Char.isAlpha c orelse Char.isDigit c)
                      andalso Char.isHexDigit c
                              = (Char.isDigit c
                                 orelse (#"a" <= c andalso c <= #"f")
                                 orelse (#"A" <= c andalso c <= #"F"))
                      andalso Char.isGraph c = (#"!" <= c andalso c <= #"~")
                      andalso Char.isPrint c = (Char.isGraph c orelse c = #" ")
                      andalso Char.isPunct c
                              = (Char.isGraph c andalso not (Char.isAlphaNum c))
                      andalso Char.isCntrl c
                              = (Char.isAscii c andalso not (Char.isPrint c))
                      andalso Char.isSpace c
                              = ((#"\t" <= c andalso c <= #"\r") orelse c = #" ")
                      andalso Char.isAscii c
                              = (0 <= Char.ord c andalso Char.ord c <= 127)),

          P.forAll ("case conversion shifts by 32, as the Discussion gives",
                    G.asciiChar, Show.char,
                    fn c =>
                      Char.toLower c
                      = (if Char.isUpper c then Char.chr (Char.ord c + 32) else c)
                      andalso Char.toUpper c
                              = (if Char.isLower c then Char.chr (Char.ord c - 32)
                                 else c)),

          P.forAll ("isAscii is a test on the code, at any width",
                    G.char, Show.char,
                    fn c => Char.isAscii c = (Char.ord c <= 127)),

          (* toString and toCString are tabulated in the specification; these
           * check the table entry for every character, not a sample. *)
          P.forAll ("toString follows the specification's table",
                    G.map Char.chr (G.int (0, Int.min (maxOrd, 999))), Show.char,
                    fn c => Char.toString c = specToString c),

          P.forAll ("toCString follows the specification's table",
                    G.map Char.chr (G.int (0, Int.min (maxOrd, 255))), Show.char,
                    fn c => Char.toCString c = specToCString c),

          P.forAll ("scan reads back what toString wrote, and consumes it all",
                    G.char, Show.char,
                    fn c =>
                      case Char.scan Substring.getc
                                     (Substring.full (Char.toString c ^ "!")) of
                          NONE => false
                        | SOME (d, rest) =>
                            d = c andalso Substring.string rest = "!"),

          (* "The function fromString is equivalent to StringCvt.scanString
           * scan." *)
          P.forAll ("fromString is scanString scan",
                    G.oneOf [ G.map Char.toString G.char,
                              G.printableString ],
                    Show.string,
                    fn s =>
                      Char.fromString s = StringCvt.scanString Char.scan s),

          P.forAll ("succ and pred are chr of the neighbouring code",
                    G.map Char.chr (G.int (1, maxOrd - 1)), Show.char,
                    fn c =>
                      Char.succ c = Char.chr (Char.ord c + 1)
                      andalso Char.pred c = Char.chr (Char.ord c - 1)),

          P.forAll ("succ and pred are inverse in the interior",
                    G.map Char.chr (G.int (1, maxOrd - 1)), Show.char,
                    fn c => Char.pred (Char.succ c) = c
                            andalso Char.succ (Char.pred c) = c)
        ])
      ])
  end
