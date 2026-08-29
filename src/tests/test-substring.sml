(* Tests for the Substring structure.
 *
 * The point of a substring is that it denotes a window on an existing string
 * without copying it, so the tests keep checking `base` as well as `string`:
 * an implementation that quietly copies would still pass the content tests
 * but would change the base string and the offsets.
 *)

functor SubstringTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure SS = Substring

    val str = G.asciiString
    val showS = Show.string
    val comma = fn c => c = #","

    val showBase = Show.triple (Show.string, Show.int, Show.int)
    val eqBase = A.eqBy (op =, showBase)

    (* An arbitrary window on an arbitrary string, as a substring plus the
     * pieces it was cut from, so that laws can be stated about all three. *)
    val windowed =
      G.bind str (fn s =>
        G.bind (G.int (0, String.size s)) (fn i =>
          G.map (fn n => (s, i, n)) (G.int (0, String.size s - i))))

    val showWindowed = Show.triple (showS, Show.int, Show.int)

    fun ssOf (s, i, n) = SS.substring (s, i, n)

    val suite = Group ("Substring",
      [ Group ("construction",
        [ Case ("full covers the whole string", fn () =>
            (A.eqString "content" ("abc", SS.string (SS.full "abc"));
             eqBase "base" (("abc", 0, 3), SS.base (SS.full "abc")))),

          Case ("substring cuts a window", fn () =>
            (A.eqString "content" ("bc", SS.string (SS.substring ("abcde", 1, 2)));
             eqBase "base keeps the original string"
               (("abcde", 1, 2), SS.base (SS.substring ("abcde", 1, 2))))),

          Case ("substring rejects windows off the end", fn () =>
            (A.raises "too long" A.isSubscript
               (fn () => SS.substring ("abc", A.hide 1, A.hide 3));
             A.raises "negative start" A.isSubscript
               (fn () => SS.substring ("abc", A.hide ~1, A.hide 1));
             A.raises "negative length" A.isSubscript
               (fn () => SS.substring ("abc", A.hide 1, A.hide ~1)))),

          Case ("extract to the end", fn () =>
            (A.eqString "suffix" ("bcde", SS.string (SS.extract ("abcde", 1, NONE)));
             A.eqString "explicit length"
               ("bc", SS.string (SS.extract ("abcde", 1, SOME 2)));
             A.eqString "starting at the end is legal"
               ("", SS.string (SS.extract ("abcde", 5, NONE)));
             A.raises "past the end" A.isSubscript
               (fn () => SS.extract ("abcde", A.hide 6, NONE)))),

          Case ("slice narrows an existing substring", fn () =>
            let
              val ss = SS.substring ("abcdef", 1, 4)   (* "bcde" *)
            in
              A.eqString "narrowed" ("cd", SS.string (SS.slice (ss, 1, SOME 2)));
              eqBase "offsets are relative to the original base"
                (("abcdef", 2, 2), SS.base (SS.slice (ss, 1, SOME 2)));
              A.eqString "to the end" ("cde", SS.string (SS.slice (ss, 1, NONE)));
              A.raises "outside the window" A.isSubscript
                (fn () => SS.slice (ss, A.hide 1, SOME 4))
            end),

          Case ("size and isEmpty", fn () =>
            (A.eqInt "size" (2, SS.size (SS.substring ("abcde", 1, 2)));
             A.eqBool "not empty" (false, SS.isEmpty (SS.full "a"));
             A.eqBool "empty" (true, SS.isEmpty (SS.full ""));
             A.eqBool "empty window on a non-empty string"
               (true, SS.isEmpty (SS.substring ("abc", 1, 0))))),

          Case ("sub", fn () =>
            let
              val ss = SS.substring ("abcde", 1, 3)   (* "bcd" *)
            in
              A.eqChar "index is relative to the window" (#"b", SS.sub (ss, 0));
              A.eqChar "last" (#"d", SS.sub (ss, 2));
              A.raises "past the window" A.isSubscript (fn () => SS.sub (ss, A.hide 3));
              A.raises "negative" A.isSubscript (fn () => SS.sub (ss, A.hide ~1))
            end)
        ]),

        Group ("scanning",
        [ Case ("getc", fn () =>
            (case SS.getc (SS.full "ab") of
                 NONE => A.fail "expected a character"
               | SOME (c, rest) =>
                   (A.eqChar "first" (#"a", c);
                    A.eqString "rest" ("b", SS.string rest));
             A.eqBy (op =, Show.option (Show.pair (Show.char, Show.string)))
               "empty"
               (NONE, Option.map (fn (c, r) => (c, SS.string r))
                                 (SS.getc (SS.full ""))))),

          Case ("first", fn () =>
            (A.eqCharOption "non-empty" (SOME #"a", SS.first (SS.full "abc"));
             A.eqCharOption "empty" (NONE, SS.first (SS.full "")))),

          Case ("triml and trimr", fn () =>
            let
              val ss = SS.full "abcde"
            in
              A.eqString "triml" ("cde", SS.string (SS.triml 2 ss));
              A.eqString "trimr" ("abc", SS.string (SS.trimr 2 ss));
              A.eqString "triml beyond the end is empty"
                ("", SS.string (SS.triml 99 ss));
              A.eqString "trimr beyond the end is empty"
                ("", SS.string (SS.trimr 99 ss));
              A.raises "negative triml" A.isSubscript (fn () => SS.triml ~1 ss);
              A.raises "negative trimr" A.isSubscript (fn () => SS.trimr ~1 ss)
            end),

          Case ("splitAt", fn () =>
            let
              val (l, r) = SS.splitAt (SS.full "abcde", 2)
            in
              A.eqString "left" ("ab", SS.string l);
              A.eqString "right" ("cde", SS.string r);
              A.raises "past the end" A.isSubscript
                (fn () => SS.splitAt (SS.full "abc", A.hide 4))
            end),

          Case ("splitl splits at the first character failing the predicate",
            fn () =>
              let
                val (l, r) = SS.splitl Char.isAlpha (SS.full "ab1cd")
              in
                A.eqString "left" ("ab", SS.string l);
                A.eqString "right" ("1cd", SS.string r)
              end),

          Case ("splitr splits at the last character failing the predicate",
            fn () =>
              let
                val (l, r) = SS.splitr Char.isAlpha (SS.full "ab1cd")
              in
                A.eqString "left" ("ab1", SS.string l);
                A.eqString "right" ("cd", SS.string r)
              end),

          Case ("takel, dropl, taker, dropr", fn () =>
            let
              val ss = SS.full "ab1cd"
            in
              A.eqString "takel" ("ab", SS.string (SS.takel Char.isAlpha ss));
              A.eqString "dropl" ("1cd", SS.string (SS.dropl Char.isAlpha ss));
              A.eqString "taker" ("cd", SS.string (SS.taker Char.isAlpha ss));
              A.eqString "dropr" ("ab1", SS.string (SS.dropr Char.isAlpha ss))
            end),

          Case ("position finds the first occurrence", fn () =>
            let
              val (pre, suf) = SS.position "cd" (SS.full "abcdcd")
            in
              A.eqString "before" ("ab", SS.string pre);
              A.eqString "from the match on" ("cdcd", SS.string suf)
            end),

          Case ("position with no occurrence puts everything on the left",
            fn () =>
              let
                val (pre, suf) = SS.position "zz" (SS.full "abc")
              in
                A.eqString "before" ("abc", SS.string pre);
                A.eqString "after" ("", SS.string suf)
              end),

          Case ("span joins two windows on the same base", fn () =>
            let
              val s = "abcdef"
              val l = SS.substring (s, 1, 2)   (* "bc" *)
              val r = SS.substring (s, 3, 2)   (* "de" *)
            in
              A.eqString "spanned" ("bcde", SS.string (SS.span (l, r)));
              eqBase "base" ((s, 1, 4), SS.base (SS.span (l, r)))
            end),

          Case ("span rejects windows on different strings", fn () =>
            A.raises "different bases" A.isSpan
              (fn () => SS.span (SS.full "abc", SS.full "def")))
        ]),

        Group ("traversal",
        [ Case ("app visits the window only", fn () =>
            let
              val seen = ref []
            in
              SS.app (fn c => seen := c :: !seen) (SS.substring ("abcde", 1, 3));
              A.eqCharList "visited" ([#"d", #"c", #"b"], !seen)
            end),

          Case ("foldl and foldr", fn () =>
            let
              val ss = SS.substring ("abcde", 1, 3)   (* "bcd" *)
            in
              A.eqString "foldl builds the reverse"
                ("dcb", SS.foldl (fn (c, acc) => String.str c ^ acc) "" ss);
              A.eqString "foldr keeps the order"
                ("bcd", SS.foldr (fn (c, acc) => String.str c ^ acc) "" ss)
            end),

          Case ("explode and translate", fn () =>
            (A.eqCharList "explode"
               ([#"b", #"c"], SS.explode (SS.substring ("abcde", 1, 2)));
             A.eqString "translate"
               ("BC", SS.translate (String.str o Char.toUpper)
                                   (SS.substring ("abcde", 1, 2))))),

          Case ("concat and concatWith", fn () =>
            (A.eqString "concat"
               ("bcd", SS.concat [SS.substring ("abc", 1, 2),
                                  SS.substring ("xdz", 1, 1)]);
             A.eqString "concatWith"
               ("bc-d", SS.concatWith "-" [SS.substring ("abc", 1, 2),
                                           SS.substring ("xdz", 1, 1)]))),

          Case ("fields and tokens", fn () =>
            (A.eqStringList "fields"
               (["a", "", "b"],
                List.map SS.string (SS.fields comma (SS.full "a,,b")));
             A.eqStringList "tokens"
               (["a", "b"],
                List.map SS.string (SS.tokens comma (SS.full "a,,b")))))
        ]),

        Group ("comparison",
        [ Case ("compare looks only at the window", fn () =>
            (A.eqOrder "equal content on different bases"
               (EQUAL, SS.compare (SS.substring ("xabz", 1, 2), SS.full "ab"));
             A.eqOrder "less" (LESS, SS.compare (SS.full "ab", SS.full "b")))),

          Case ("isPrefix, isSuffix, isSubstring", fn () =>
            (A.eqBool "prefix" (true, SS.isPrefix "ab" (SS.full "abc"));
             A.eqBool "suffix" (true, SS.isSuffix "bc" (SS.full "abc"));
             A.eqBool "substring" (true, SS.isSubstring "b" (SS.full "abc"));
             A.eqBool "not a prefix of the window"
               (false, SS.isPrefix "ab" (SS.substring ("xabz", 2, 2))))),

          Case ("collate", fn () =>
            A.eqOrder "case-insensitive" (EQUAL,
              SS.collate (fn (a, b) => Char.compare (Char.toLower a, Char.toLower b))
                         (SS.full "AB", SS.full "ab")))
        ]),

        Group ("laws",
        [ P.forAll ("string inverts full", str, showS,
                    fn s => SS.string (SS.full s) = s),

          P.forAll ("full spans the whole base", str, showS,
                    fn s => SS.base (SS.full s) = (s, 0, String.size s)),

          P.forAll ("size agrees with the string it denotes",
                    windowed, showWindowed,
                    fn w => SS.size (ssOf w) = String.size (SS.string (ssOf w))),

          P.forAll ("a window denotes the corresponding String.substring",
                    windowed, showWindowed,
                    fn (s, i, n) =>
                      SS.string (SS.substring (s, i, n))
                      = String.substring (s, i, n)),

          P.forAll ("base recovers the arguments of substring",
                    windowed, showWindowed,
                    fn (s, i, n) => SS.base (SS.substring (s, i, n)) = (s, i, n)),

          P.forAll ("cutting a window does not copy the base",
                    windowed, showWindowed,
                    fn (s, i, n) =>
                      let val (b, _, _) = SS.base (SS.substring (s, i, n))
                      in b = s end),

          P.forAll ("splitAt reassembles",
                    G.bind str (fn s =>
                      G.map (fn k => (s, k)) (G.int (0, String.size s))),
                    Show.pair (showS, Show.int),
                    fn (s, k) =>
                      let val (l, r) = SS.splitAt (SS.full s, k)
                      in SS.string l ^ SS.string r = s end),

          P.forAll ("splitl reassembles and splits at the predicate",
                    str, showS,
                    fn s =>
                      let
                        val (l, r) = SS.splitl Char.isAlpha (SS.full s)
                      in
                        SS.string l ^ SS.string r = s
                        andalso List.all Char.isAlpha (SS.explode l)
                        andalso (SS.isEmpty r
                                 orelse not (Char.isAlpha (SS.sub (r, 0))))
                      end),

          P.forAll ("splitr reassembles", str, showS,
                    fn s =>
                      let val (l, r) = SS.splitr Char.isAlpha (SS.full s)
                      in SS.string l ^ SS.string r = s end),

          P.forAll ("takel and dropl are the halves of splitl", str, showS,
                    fn s =>
                      let val ss = SS.full s
                      in
                        (SS.string (SS.takel Char.isAlpha ss),
                         SS.string (SS.dropl Char.isAlpha ss))
                        = (fn (l, r) => (SS.string l, SS.string r))
                            (SS.splitl Char.isAlpha ss)
                      end),

          P.forAll ("taker and dropr are the halves of splitr", str, showS,
                    fn s =>
                      let val ss = SS.full s
                      in
                        (SS.string (SS.dropr Char.isAlpha ss),
                         SS.string (SS.taker Char.isAlpha ss))
                        = (fn (l, r) => (SS.string l, SS.string r))
                            (SS.splitr Char.isAlpha ss)
                      end),

          P.forAll ("position reassembles the string",
                    G.pair (str, G.resize 3 G.asciiString),
                    Show.pair (showS, showS),
                    fn (s, pat) =>
                      let val (pre, suf) = SS.position pat (SS.full s)
                      in SS.string pre ^ SS.string suf = s end),

          P.forAll ("position finds the pattern when it is there",
                    G.triple (G.resize 4 str, G.resize 3 G.asciiString,
                              G.resize 4 str),
                    Show.triple (showS, showS, showS),
                    fn (a, b, c) =>
                      let
                        val s = a ^ b ^ c
                        val (_, suf) = SS.position b (SS.full s)
                      in
                        SS.isPrefix b suf
                      end),

          P.forAll ("triml and trimr are complementary",
                    G.bind str (fn s =>
                      G.map (fn k => (s, k)) (G.int (0, String.size s))),
                    Show.pair (showS, Show.int),
                    fn (s, k) =>
                      SS.string (SS.triml k (SS.full s))
                      = String.extract (s, k, NONE)),

          P.forAll ("explode agrees with the string's explosion",
                    windowed, showWindowed,
                    fn w => SS.explode (ssOf w) = String.explode (SS.string (ssOf w))),

          P.forAll ("concat of the fields with separators is the original",
                    str, showS,
                    fn s =>
                      String.concatWith ","
                        (List.map SS.string (SS.fields comma (SS.full s)))
                      = s),

          P.forAll ("compare ignores the base",
                    G.pair (str, str), Show.pair (showS, showS),
                    fn (a, b) =>
                      SS.compare (SS.full a, SS.full b) = String.compare (a, b)),

          P.forAll ("foldr rebuilds the character list", windowed, showWindowed,
                    fn w => SS.foldr (op ::) [] (ssOf w) = SS.explode (ssOf w)),

          P.forAll ("span of a window with itself is that window",
                    windowed, showWindowed,
                    fn w =>
                      let val ss = ssOf w
                      in SS.string (SS.span (ss, ss)) = SS.string ss end)
        ])
      ])
  end
