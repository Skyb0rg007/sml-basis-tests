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
               (fn () => String.extract ("abcde", A.hide 6, NONE))))
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
               (SOME "a\nb", String.fromCString "a\\nb")))
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
                    fn s => String.fromCString (String.toCString s) = SOME s)
        ])
      ])
  end
