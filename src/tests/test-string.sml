(* Tests for the String structure. *)

functor StringTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val str = G.asciiString
    val showS = Show.string
    val pairS = G.pair (str, str)
    val showPairS = Show.pair (showS, showS)
    val comma = fn c => c = #","
    val isComma = #","

    (* A string together with a legal index into it. *)
    val stringAndIndex =
      G.bind (G.filter (fn s => String.size s > 0) str) (fn s =>
        G.map (fn i => (s, i)) (G.int (0, String.size s - 1)))

    (* A string with a legal (start, length) window. *)
    val stringAndWindow =
      G.bind str (fn s =>
        G.bind (G.int (0, String.size s)) (fn i =>
          G.map (fn n => (s, i, n)) (G.int (0, String.size s - i))))

    val showWindow = Show.triple (showS, Show.int, Show.int)

    val suite = Group ("String",
      [ Group ("basics",
        [ Case ("size", fn () =>
            (A.eqInt "empty" (0, String.size "");
             A.eqInt "three" (3, String.size "abc"))),

          Case ("maxSize is non-negative", fn () =>
            A.that "maxSize >= 0" (String.maxSize >= 0)),

          Case ("sub", fn () =>
            (A.eqChar "first" (#"a", String.sub ("abc", 0));
             A.eqChar "last" (#"c", String.sub ("abc", 2));
             A.raises "past the end" A.isSubscript
               (fn () => String.sub ("abc", A.hide 3));
             A.raises "negative" A.isSubscript
               (fn () => String.sub ("abc", A.hide ~1));
             A.raises "into the empty string" A.isSubscript
               (fn () => String.sub ("", A.hide 0)))),

          Case ("str makes a one-character string", fn () =>
            A.eqString "str" ("a", String.str #"a")),

          Case ("concatenation", fn () =>
            (A.eqString "both" ("abcdef", "abc" ^ "def");
             A.eqString "left empty" ("def", "" ^ "def");
             A.eqString "right empty" ("abc", "abc" ^ ""))),

          Case ("concat", fn () =>
            (A.eqString "several" ("abcdef", String.concat ["ab", "", "cdef"]);
             A.eqString "none" ("", String.concat []))),

          Case ("concatWith", fn () =>
            (A.eqString "separated" ("a,b,c", String.concatWith "," ["a", "b", "c"]);
             A.eqString "single element has no separator"
               ("a", String.concatWith "," ["a"]);
             A.eqString "empty list" ("", String.concatWith "," []);
             A.eqString "empty elements still separate"
               (",,", String.concatWith "," ["", "", ""]))),

          Case ("implode and explode", fn () =>
            (A.eqString "implode" ("abc", String.implode [#"a", #"b", #"c"]);
             A.eqString "implode nothing" ("", String.implode []);
             A.eqCharList "explode" ([#"a", #"b", #"c"], String.explode "abc");
             A.eqCharList "explode nothing" ([], String.explode "")))
        ]),

        Group ("extraction",
        [ Case ("substring", fn () =>
            (A.eqString "middle" ("bc", String.substring ("abcde", 1, 2));
             A.eqString "whole" ("abcde", String.substring ("abcde", 0, 5));
             A.eqString "empty at the end" ("", String.substring ("abcde", 5, 0));
             A.raises "past the end" A.isSubscript
               (fn () => String.substring ("abcde", A.hide 3, A.hide 3));
             A.raises "negative start" A.isSubscript
               (fn () => String.substring ("abcde", A.hide ~1, A.hide 2));
             A.raises "negative length" A.isSubscript
               (fn () => String.substring ("abcde", A.hide 1, A.hide ~1)))),

          Case ("extract with an explicit length", fn () =>
            A.eqString "middle" ("bc", String.extract ("abcde", 1, SOME 2))),

          Case ("extract to the end", fn () =>
            (A.eqString "suffix" ("bcde", String.extract ("abcde", 1, NONE));
             A.eqString "starting at the end is legal"
               ("", String.extract ("abcde", 5, NONE));
             A.raises "past the end" A.isSubscript
               (fn () => String.extract ("abcde", A.hide 6, NONE)))),

          Case ("extract checks both bounds", fn () =>
            (A.raises "negative start" A.isSubscript
               (fn () => String.extract ("abcde", A.hide ~1, SOME 2));
             A.raises "negative length" A.isSubscript
               (fn () => String.extract ("abcde", A.hide 1, SOME (A.hide ~1)));
             A.raises "start plus length past the end" A.isSubscript
               (fn () => String.extract ("abcde", A.hide 3, SOME (A.hide 3)));
             A.raises "negative start with no length" A.isSubscript
               (fn () => String.extract ("abcde", A.hide ~1, NONE)))),

          (* "Implementations of these functions must perform bounds checking
           * in such a way that the Overflow exception is not raised." *)
          Case ("bounds checking does not overflow", fn () =>
            case Int.maxInt of
                NONE => ()
              | SOME big =>
                  (A.raises "substring at a huge index" A.isSubscript
                     (fn () => String.substring ("abcde", A.hide big, A.hide 1));
                   A.raises "substring of a huge length" A.isSubscript
                     (fn () => String.substring ("abcde", A.hide 1, A.hide big)))),

          Case ("extract with an explicit length is substring", fn () =>
            A.eqString "the same window"
              (String.substring ("abcde", 1, 2),
               String.extract ("abcde", 1, SOME 2)))
        ]
        (* The same bounds requirement for extract, which is where SML/NJ
         * 2026.1 crashes the runtime rather than raising; see
         * canExtractAtHugeIndex. *)
        @ onlyIf (C.canExtractAtHugeIndex,
                  "implementation not declared safe at an index near maxInt")
        [ Case ("extract checks a huge index without overflowing", fn () =>
            case Int.maxInt of
                NONE => ()
              | SOME big =>
                  (A.raises "extract at a huge index" A.isSubscript
                     (fn () => String.extract ("abcde", A.hide big, SOME (A.hide 1)));
                   A.raises "extract of a huge length" A.isSubscript
                     (fn () => String.extract ("abcde", A.hide 1, SOME (A.hide big)))))
        ]),

        Group ("searching and splitting",
        [ Case ("isPrefix", fn () =>
            (A.eqBool "prefix" (true, String.isPrefix "ab" "abc");
             A.eqBool "whole string" (true, String.isPrefix "abc" "abc");
             A.eqBool "empty prefix" (true, String.isPrefix "" "abc");
             A.eqBool "not a prefix" (false, String.isPrefix "bc" "abc");
             A.eqBool "longer than the string" (false, String.isPrefix "abcd" "abc"))),

          Case ("isSuffix", fn () =>
            (A.eqBool "suffix" (true, String.isSuffix "bc" "abc");
             A.eqBool "empty suffix" (true, String.isSuffix "" "abc");
             A.eqBool "not a suffix" (false, String.isSuffix "ab" "abc"))),

          (* "Note that the empty string is a prefix, substring, and suffix of
           * any string, and that a string is a prefix, substring, and suffix
           * of itself." *)
          Case ("the empty string and the string itself are always found",
            fn () =>
              (A.eqBool "empty in empty, prefix" (true, String.isPrefix "" "");
               A.eqBool "empty in empty, substring"
                 (true, String.isSubstring "" "");
               A.eqBool "empty in empty, suffix" (true, String.isSuffix "" "");
               A.eqBool "a string is its own prefix"
                 (true, String.isPrefix "abc" "abc");
               A.eqBool "a string is its own substring"
                 (true, String.isSubstring "abc" "abc");
               A.eqBool "a string is its own suffix"
                 (true, String.isSuffix "abc" "abc"))),

          Case ("isSubstring", fn () =>
            (A.eqBool "inside" (true, String.isSubstring "bc" "abcd");
             A.eqBool "at the start" (true, String.isSubstring "ab" "abcd");
             A.eqBool "at the end" (true, String.isSubstring "cd" "abcd");
             A.eqBool "empty" (true, String.isSubstring "" "abcd");
             A.eqBool "absent" (false, String.isSubstring "bd" "abcd"))),

          Case ("fields keeps empty fields", fn () =>
            (A.eqStringList "simple" (["a", "b"], String.fields comma "a,b");
             A.eqStringList "adjacent separators"
               (["a", "", "b"], String.fields comma "a,,b");
             A.eqStringList "leading separator"
               (["", "a"], String.fields comma ",a");
             A.eqStringList "trailing separator"
               (["a", ""], String.fields comma "a,");
             A.eqStringList "the empty string is one empty field"
               ([""], String.fields comma ""))),

          (* "if the only delimiter is the character #"|", then the string
           * "|abc||def" contains two tokens "abc" and "def", whereas it
           * contains the four fields "", "abc", "" and "def"." *)
          Case ("the worked example from the specification", fn () =>
            let
              val bar = fn c => c = #"|"
            in
              A.eqStringList "tokens" (["abc", "def"], String.tokens bar "|abc||def");
              A.eqStringList "fields"
                (["", "abc", "", "def"], String.fields bar "|abc||def")
            end),

          Case ("tokens discards empty fields", fn () =>
            (A.eqStringList "simple" (["a", "b"], String.tokens comma "a,b");
             A.eqStringList "adjacent separators"
               (["a", "b"], String.tokens comma "a,,b");
             A.eqStringList "leading and trailing"
               (["a"], String.tokens comma ",a,");
             A.eqStringList "the empty string has no tokens"
               ([], String.tokens comma "");
             A.eqStringList "separators only"
               ([], String.tokens comma ",,,")))
        ]),

        Group ("transformation",
        [ Case ("map", fn () =>
            (A.eqString "upper case" ("ABC", String.map Char.toUpper "abc");
             A.eqString "empty" ("", String.map Char.toUpper ""))),

          Case ("translate", fn () =>
            (A.eqString "doubling" ("aabbcc",
               String.translate (fn c => String.str c ^ String.str c) "abc");
             A.eqString "deleting" ("", String.translate (fn _ => "") "abc")))
        ]),

        Group ("ordering",
        [ Case ("compare", fn () =>
            (A.eqOrder "less" (LESS, String.compare ("abc", "abd"));
             A.eqOrder "equal" (EQUAL, String.compare ("abc", "abc"));
             A.eqOrder "greater" (GREATER, String.compare ("abd", "abc"));
             A.eqOrder "a prefix is less" (LESS, String.compare ("ab", "abc"));
             A.eqOrder "empty against non-empty" (LESS, String.compare ("", "a")))),

          Case ("the comparison operators", fn () =>
            (A.eqBool "less" (true, "abc" < "abd");
             A.eqBool "less or equal" (true, "abc" <= "abc");
             A.eqBool "greater" (true, "abd" > "abc");
             A.eqBool "greater or equal" (true, "abc" >= "abc"))),

          Case ("collate with a custom character order", fn () =>
            (A.eqOrder "case-insensitive equality" (EQUAL,
               String.collate (fn (a, b) =>
                                 Char.compare (Char.toLower a, Char.toLower b))
                              ("ABC", "abc"));
             A.eqOrder "ordinal comparison differs"
               (LESS, String.collate Char.compare ("ABC", "abc"))))
        ]),

        Group ("conversion to and from text",
        [ Case ("toString escapes", fn () =>
            (A.eqString "plain" ("abc", String.toString "abc");
             A.eqString "newline" ("a\\nb", String.toString "a\nb");
             A.eqString "quote and backslash"
               ("\\\"\\\\", String.toString "\"\\"))),

          Case ("fromString", fn () =>
            (A.eqStringOption "plain" (SOME "abc", String.fromString "abc");
             A.eqStringOption "newline escape"
               (SOME "a\nb", String.fromString "a\\nb");
             A.eqStringOption "empty" (SOME "", String.fromString ""))),

          (* The \...\ gap is skipped, so it must vanish from the result. *)
          Case ("fromString honours the escape gap", fn () =>
            A.eqStringOption "gap spanning whitespace"
              (SOME "ab", String.fromString "a\\   \\b")),

          Case ("toCString and fromCString", fn () =>
            (A.eqString "toCString" ("a\\nb", String.toCString "a\nb");
             A.eqStringOption "fromCString"
               (SOME "a\nb", String.fromCString "a\\nb"))),

          (* The samples the specification tabulates for String.fromString.
           * They differ from CHAR.fromString's: a prefix that scans to
           * nothing still returns SOME "". *)
          Case ("the sample conversions from the specification", fn () =>
            (A.eqStringOption "an illegal escape" (NONE, String.fromString "\\q");
             A.eqStringOption "a letter then a control character"
               (SOME "a", String.fromString "a\^D");
             A.eqStringOption "a letter then a formatting sequence"
               (SOME "a", String.fromString "a\\ \\\\q");
             A.eqStringOption "a formatting sequence alone"
               (SOME "", String.fromString "\\ \\");
             A.eqStringOption "the empty string" (SOME "", String.fromString "");
             A.eqStringOption "a formatting sequence then a control character"
               (SOME "", String.fromString "\\ \\\^D");
             A.eqStringOption "an unterminated formatting sequence"
               (NONE, String.fromString "\\ a");
             A.eqStringOption "a lone control character"
               (NONE, String.fromString "\^D"))),

          (* "They do not skip leading whitespace."  A space is printable, so
           * it is scanned like any other character; a tab is not, and since
           * nothing at all can be scanned before it the result is NONE
           * rather than SOME "". *)
          Case ("fromString keeps leading whitespace", fn () =>
            (A.eqStringOption "spaces are ordinary printable characters"
               (SOME "  ab", String.fromString "  ab");
             A.eqStringOption "a leading tab cannot be scanned at all"
               (NONE, String.fromString "\tab");
             A.eqStringOption "a leading newline cannot be scanned at all"
               (NONE, String.fromString "\nab"))),

          Case ("fromString stops at a non-printable character", fn () =>
            A.eqStringOption "up to the control character"
              (SOME "ab", String.fromString ("ab" ^ String.str (Char.chr 4) ^ "cd"))),

          Case ("fromCString rejects an unescaped double quote", fn () =>
            (A.eqStringOption "a bare single quote is accepted"
               (SOME "a'b", String.fromCString "a'b");
             A.eqStringOption "a bare double quote stops the scan"
               (SOME "a", String.fromCString "a\"b")))
        ]
        (* String.scan reads the body of an SML string literal, decoding
         * escapes as it goes, and consumes as much as it can.
         *
         * On a build where src/compat supplies String.scan because the
         * implementation does not have it, these two would be testing this
         * suite's own code and are skipped instead. *)
        @ onlyIf (not (Compat.isSubstituted "String.scan"),
                  "String.scan is supplied by src/compat on this build")
        [ Case ("scan reads an escaped literal", fn () =>
            case String.scan Substring.getc (Substring.full "ab\\ncd") of
                NONE => A.fail "scan returned NONE"
              | SOME (v, rest) =>
                  (A.eqString "decoded" ("ab\ncd", v);
                   A.eqString "nothing left" ("", Substring.string rest))),

          Case ("scan stops at something it cannot read", fn () =>
            case String.scan Substring.getc (Substring.full "ab\\q") of
                NONE => A.fail "scan returned NONE"
              | SOME (v, rest) =>
                  (A.eqString "the part it could read" ("ab", v);
                   A.eqString "and the rest is left"
                     ("\\q", Substring.string rest)))
        ]),

        Group ("laws",
        [ P.forAll ("implode inverts explode", str, showS,
                    fn s => String.implode (String.explode s) = s),

          P.forAll ("explode inverts implode", G.list G.asciiChar, Show.charList,
                    fn cs => String.explode (String.implode cs) = cs),

          P.forAll ("size is additive over concatenation", pairS, showPairS,
                    fn (a, b) => String.size (a ^ b) = String.size a + String.size b),

          P.forAll ("concatenation is associative",
                    G.triple (str, str, str), Show.triple (showS, showS, showS),
                    fn (a, b, c) => (a ^ b) ^ c = a ^ (b ^ c)),

          P.forAll ("the empty string is a unit", str, showS,
                    fn s => "" ^ s = s andalso s ^ "" = s),

          P.forAll ("concat is a fold of concatenation",
                    G.list str, Show.list showS,
                    fn ss => String.concat ss = List.foldr op^ "" ss),

          P.forAll ("concatWith with an empty separator is concat",
                    G.list str, Show.list showS,
                    fn ss => String.concatWith "" ss = String.concat ss),

          P.forAll ("sub agrees with explode", stringAndIndex,
                    Show.pair (showS, Show.int),
                    fn (s, i) => String.sub (s, i) = List.nth (String.explode s, i)),

          P.forAll ("substring of the whole string is the string", str, showS,
                    fn s => String.substring (s, 0, String.size s) = s),

          P.forAll ("a substring has the requested size",
                    stringAndWindow, showWindow,
                    fn (s, i, n) => String.size (String.substring (s, i, n)) = n),

          P.forAll ("a string splits into three pieces around any window",
                    stringAndWindow, showWindow,
                    fn (s, i, n) =>
                      String.substring (s, 0, i)
                      ^ String.substring (s, i, n)
                      ^ String.extract (s, i + n, NONE)
                      = s),

          P.forAll ("extract with an explicit length is substring",
                    stringAndWindow, showWindow,
                    fn (s, i, n) =>
                      String.extract (s, i, SOME n) = String.substring (s, i, n)),

          P.forAll ("a concatenation starts with its left half",
                    pairS, showPairS,
                    fn (a, b) => String.isPrefix a (a ^ b)),

          P.forAll ("a concatenation ends with its right half",
                    pairS, showPairS,
                    fn (a, b) => String.isSuffix b (a ^ b)),

          P.forAll ("a concatenation contains its middle",
                    G.triple (str, str, str), Show.triple (showS, showS, showS),
                    fn (a, b, c) => String.isSubstring b (a ^ b ^ c)),

          P.forAll ("a prefix is also a substring", pairS, showPairS,
                    fn (a, b) =>
                      P.implies (String.isPrefix a b, String.isSubstring a b)),

          P.forAll ("map preserves size", str, showS,
                    fn s => String.size (String.map Char.toUpper s) = String.size s),

          P.forAll ("map is translate of a single character", str, showS,
                    fn s =>
                      String.map Char.toUpper s
                      = String.translate (String.str o Char.toUpper) s),

          P.forAll ("translate is concat of the mapped explosion", str, showS,
                    fn s =>
                      let val f = fn c => String.str c ^ "-"
                      in
                        String.translate f s
                        = String.concat (List.map f (String.explode s))
                      end),

          P.forAll ("fields rejoined with the separator is the original",
                    str, showS,
                    fn s => String.concatWith "," (String.fields comma s) = s),

          P.forAll ("fields always yields one more piece than separators",
                    str, showS,
                    fn s =>
                      List.length (String.fields comma s)
                      = 1 + List.length (List.filter comma (String.explode s))),

          P.forAll ("tokens is fields without the empty pieces", str, showS,
                    fn s =>
                      String.tokens comma s
                      = List.filter (fn f => f <> "") (String.fields comma s)),

          P.forAll ("no token contains a separator", str, showS,
                    fn s =>
                      List.all (fn t => not (Char.contains t isComma))
                               (String.tokens comma s)),

          P.forAll ("compare is the collation of the explosions",
                    pairS, showPairS,
                    fn (a, b) =>
                      String.compare (a, b)
                      = List.collate Char.compare
                          (String.explode a, String.explode b)),

          P.forAll ("compare agrees with the comparison operators",
                    pairS, showPairS,
                    fn (a, b) =>
                      case String.compare (a, b) of
                          LESS => a < b
                        | EQUAL => a = b
                        | GREATER => a > b),

          P.forAll ("collate with Char.compare is compare", pairS, showPairS,
                    fn (a, b) =>
                      String.collate Char.compare (a, b) = String.compare (a, b)),

          P.forAll ("fromString inverts toString", str, showS,
                    fn s => String.fromString (String.toString s) = SOME s),

          P.forAll ("fromCString inverts toCString", str, showS,
                    fn s => String.fromCString (String.toCString s) = SOME s),

          (* "This is equivalent to translate Char.toString s", and likewise
           * for toCString. *)
          P.forAll ("toString is translate of Char.toString", G.string, showS,
                    fn s => String.toString s = String.translate Char.toString s),

          P.forAll ("toCString is translate of Char.toCString", G.string, showS,
                    fn s => String.toCString s = String.translate Char.toCString s),

          (* "It is equivalent to implode(List.map f (explode s))." *)
          P.forAll ("map is implode of the mapped explosion", str, showS,
                    fn s =>
                      String.map Char.toUpper s
                      = String.implode (List.map Char.toUpper (String.explode s))),

          (* "This is equivalent to concat (List.map str l)." *)
          P.forAll ("implode is concat of the singletons",
                    G.list G.asciiChar, Show.charList,
                    fn cs =>
                      String.implode cs
                      = String.concat (List.map String.str cs)),

          P.forAll ("every string contains itself and the empty string",
                    str, showS,
                    fn s =>
                      String.isPrefix s s andalso String.isSuffix s s
                      andalso String.isSubstring s s
                      andalso String.isPrefix "" s
                      andalso String.isSuffix "" s
                      andalso String.isSubstring "" s),

          P.forAll ("a suffix is also a substring", pairS, showPairS,
                    fn (a, b) =>
                      P.implies (String.isSuffix a b, String.isSubstring a b)),

          P.forAll ("isSubstring agrees with a search over the windows",
                    G.pair (G.resize 4 str, str), showPairS,
                    fn (a, b) =>
                      let
                        val n = String.size a
                        fun at i = String.substring (b, i, n) = a
                        fun search i =
                          if i + n > String.size b then false
                          else at i orelse search (i + 1)
                      in
                        String.isSubstring a b = search 0
                      end),

          (* "A token is a non-empty maximal substring of s not containing any
           * delimiter.  A field is a (possibly empty) maximal substring of s
           * not containing any delimiter." *)
          P.forAll ("no field contains a delimiter", str, showS,
                    fn s =>
                      List.all (fn f => not (Char.contains f isComma))
                               (String.fields comma s)),

          P.forAll ("every token is non-empty", str, showS,
                    fn s => List.all (fn t => t <> "") (String.tokens comma s)),

          P.forAll ("fields is tokens once the empty pieces are put back",
                    str, showS,
                    fn s =>
                      String.concatWith "," (String.fields comma s) = s
                      andalso List.all (fn t => List.exists (fn f => f = t)
                                                            (String.fields comma s))
                                       (String.tokens comma s))
        ])
      ])
  end
