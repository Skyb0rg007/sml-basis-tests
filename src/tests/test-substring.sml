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
              (fn () => SS.span (SS.full "abc", SS.full "def"))),

          (* "span returns substring(s, i, (i'+n')-i) unless s <> s' or
           * i'+n' < i ... Note that this does not preclude ss' from beginning
           * to the left of ss, or ss from ending to the right of ss'." *)
          Case ("span allows the second window to start before the first",
            fn () =>
              let
                val s = "abcdef"
                val ss = SS.substring (s, 3, 2)    (* "de" *)
                val ss' = SS.substring (s, 1, 4)   (* "bcde" *)
              in
                A.eqString "up to the end of the second"
                  ("de", SS.string (SS.span (ss, ss')));
                eqBase "base" ((s, 3, 2), SS.base (SS.span (ss, ss')))
              end),

          Case ("span rejects a second window ending before the first starts",
            fn () =>
              let
                val s = "abcdef"
              in
                A.raises "disjoint and out of order" A.isSpan
                  (fn () => SS.span (SS.substring (s, 4, 2),
                                     SS.substring (s, 0, 1)))
              end),

          (* The example the specification works through. *)
          Case ("splitl and splitr on the specification's example", fn () =>
            let
              val p = fn c => c = #"a" orelse c = #"c"
              val ss = SS.full "aaaXbbbbXccc"
              val (l1, r1) = SS.splitl p ss
              val (l2, r2) = SS.splitr p ss
            in
              A.eqString "splitl left" ("aaa", SS.string l1);
              A.eqString "splitl right" ("XbbbbXccc", SS.string r1);
              A.eqString "splitr left" ("aaaXbbbbX", SS.string l2);
              A.eqString "splitr right" ("ccc", SS.string r2)
            end),

          Case ("slice checks its arguments", fn () =>
            let
              val ss = SS.substring ("abcdef", 1, 4)   (* "bcde" *)
            in
              A.raises "negative start" A.isSubscript
                (fn () => SS.slice (ss, A.hide ~1, SOME 1));
              A.raises "negative size" A.isSubscript
                (fn () => SS.slice (ss, A.hide 1, SOME (A.hide ~1)));
              A.raises "past the window with a size" A.isSubscript
                (fn () => SS.slice (ss, A.hide 3, SOME (A.hide 2)));
              A.raises "past the window without a size" A.isSubscript
                (fn () => SS.slice (ss, A.hide 5, NONE));
              A.eqString "at the very end is empty"
                ("", SS.string (SS.slice (ss, 4, NONE)))
            end),

          Case ("splitAt rejects an index outside the window", fn () =>
            (A.raises "negative" A.isSubscript
               (fn () => SS.splitAt (SS.full "abc", A.hide ~1));
             A.raises "past the end" A.isSubscript
               (fn () => SS.splitAt (SS.full "abc", A.hide 4)))),

          (* "Implementations of these functions must perform bounds checking
           * in such a way that the Overflow exception is not raised." *)
          Case ("bounds checking does not overflow", fn () =>
            case Int.maxInt of
                NONE => ()
              | SOME big =>
                  (A.raises "substring at a huge index" A.isSubscript
                     (fn () => SS.substring ("abcde", A.hide big, A.hide 1));
                   A.raises "substring of a huge length" A.isSubscript
                     (fn () => SS.substring ("abcde", A.hide 1, A.hide big));
                   A.raises "slice of a huge length" A.isSubscript
                     (fn () => SS.slice (SS.full "abcde", A.hide 1,
                                         SOME (A.hide big)))))
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
                      in SS.string (SS.span (ss, ss)) = SS.string ss end),

          (* "It will always be the case that 0 <= i <= i + n <= |s|." *)
          P.forAll ("base always reports a window inside its string",
                    windowed, showWindowed,
                    fn w =>
                      let val (s, i, n) = SS.base (ssOf w)
                      in 0 <= i andalso 0 <= n
                         andalso i + n <= String.size s
                      end),

          (* The Discussion requires it: "Functions that extract pieces of a
           * substring, such as splitl or tokens must return substrings with
           * the same base string.  This requirement is particularly important
           * if span is to be used to put the pieces back together again." *)
          P.forAll ("the extracting functions keep the base string",
                    windowed, showWindowed,
                    fn w =>
                      let
                        val ss = ssOf w
                        val (s, _, _) = SS.base ss
                        fun sameBase piece =
                          let val (b, i, n) = SS.base piece
                          in b = s andalso 0 <= i andalso i + n <= String.size b
                          end
                        val (l, r) = SS.splitl Char.isAlpha ss
                        val (l', r') = SS.splitr Char.isAlpha ss
                        val (pre, suf) = SS.position "a" ss
                      in
                        List.all sameBase
                          ([l, r, l', r', pre, suf,
                            SS.takel Char.isAlpha ss, SS.dropl Char.isAlpha ss,
                            SS.taker Char.isAlpha ss, SS.dropr Char.isAlpha ss,
                            SS.triml 1 ss, SS.trimr 1 ss]
                           @ SS.tokens comma ss @ SS.fields comma ss)
                      end),

          (* "if we have val (s, i, n) = base ss and there is a least index
           * k >= i such that s = s'[k..k+m-1], then suff corresponds to
           * (s', k, n+i-k) and pref to (s', i, k-i); if there is no such k,
           * suff is (s', i+n, 0) and pref is (s', i, n)." *)
          P.forAll ("position reports the windows the specification names",
                    G.pair (windowed, G.resize 2 G.asciiString),
                    Show.pair (showWindowed, showS),
                    fn (w, pat) =>
                      let
                        val ss = ssOf w
                        val (s, i, n) = SS.base ss
                        val m = String.size pat
                        fun found k =
                          if k + m > i + n then NONE
                          else if String.substring (s, k, m) = pat then SOME k
                          else found (k + 1)
                        val (pre, suf) = SS.position pat ss
                      in
                        case found i of
                            SOME k =>
                              SS.base pre = (s, i, k - i)
                              andalso SS.base suf = (s, k, n + i - k)
                          | NONE =>
                              SS.base pre = (s, i, n)
                              andalso SS.base suf = (s, i + n, 0)
                      end),

          (* "for substring ss = substring(s, i, j) and k <= j, we have
           *  triml k ss = substring(s, i+k, j-k) and
           *  trimr k ss = substring(s, i, j-k)." *)
          P.forAll ("triml and trimr move the window as specified",
                    G.bind windowed (fn w =>
                      G.map (fn k => (w, k)) (G.int (0, 6))),
                    Show.pair (showWindowed, Show.int),
                    fn (w, k) =>
                      let
                        val ss = ssOf w
                        val (s, i, j) = SS.base ss
                      in
                        P.implies (k <= j,
                                   SS.base (SS.triml k ss) = (s, i + k, j - k)
                                   andalso SS.base (SS.trimr k ss)
                                           = (s, i, j - k))
                      end),

          P.forAll ("trimming beyond the window empties it",
                    windowed, showWindowed,
                    fn w =>
                      let
                        val ss = ssOf w
                        val k = SS.size ss + 1
                      in
                        SS.isEmpty (SS.triml k ss)
                        andalso SS.isEmpty (SS.trimr k ss)
                      end),

          (* Each of these is specified as its String counterpart applied to
           * `string ss`. *)
          P.forAll ("string is String.substring of base", windowed, showWindowed,
                    fn w =>
                      let val (s, i, n) = SS.base (ssOf w)
                      in SS.string (ssOf w) = String.substring (s, i, n) end),

          P.forAll ("size is the third component of base and the size of the string",
                    windowed, showWindowed,
                    fn w =>
                      let val (_, _, n) = SS.base (ssOf w)
                      in SS.size (ssOf w) = n
                         andalso SS.size (ssOf w)
                                 = String.size (SS.string (ssOf w))
                      end),

          P.forAll ("isEmpty is a test on the size", windowed, showWindowed,
                    fn w => SS.isEmpty (ssOf w) = (SS.size (ssOf w) = 0)),

          P.forAll ("sub is String.sub on the denoted string",
                    G.bind (G.filter (fn (_, _, n) => n > 0) windowed) (fn w =>
                      G.map (fn i => (w, i))
                            (G.int (0, Int.max (0, #3 w - 1)))),
                    Show.pair (showWindowed, Show.int),
                    fn (w, i) =>
                      SS.sub (ssOf w, i) = String.sub (SS.string (ssOf w), i)),

          P.forAll ("getc and first agree with the string", windowed, showWindowed,
                    fn w =>
                      let
                        val ss = ssOf w
                        val str = SS.string ss
                      in
                        (case SS.getc ss of
                             NONE => str = ""
                           | SOME (c, rest) =>
                               String.str c ^ SS.string rest = str)
                        andalso SS.first ss = (if str = "" then NONE
                                               else SOME (String.sub (str, 0)))
                      end),

          P.forAll ("the search predicates are the String ones on the window",
                    G.pair (windowed, G.resize 3 str),
                    Show.pair (showWindowed, showS),
                    fn (w, pat) =>
                      let
                        val ss = ssOf w
                        val str = SS.string ss
                      in
                        SS.isPrefix pat ss = String.isPrefix pat str
                        andalso SS.isSuffix pat ss = String.isSuffix pat str
                        andalso SS.isSubstring pat ss = String.isSubstring pat str
                      end),

          P.forAll ("collate is String.collate on the windows",
                    G.pair (windowed, windowed),
                    Show.pair (showWindowed, showWindowed),
                    fn (a, b) =>
                      SS.collate Char.compare (ssOf a, ssOf b)
                      = String.collate Char.compare
                          (SS.string (ssOf a), SS.string (ssOf b))),

          P.forAll ("concat and concatWith go through string",
                    G.list windowed, Show.list showWindowed,
                    fn ws =>
                      let val sss = List.map ssOf ws
                      in
                        SS.concat sss
                        = String.concat (List.map SS.string sss)
                        andalso SS.concatWith "-" sss
                                = String.concatWith "-" (List.map SS.string sss)
                      end),

          P.forAll ("app, foldl and foldr are the List versions over explode",
                    windowed, showWindowed,
                    fn w =>
                      let
                        val ss = ssOf w
                        val cs = SS.explode ss
                        val seen = ref []
                        val () = SS.app (fn c => seen := c :: !seen) ss
                        val f = fn (c, acc) => acc ^ String.str c
                      in
                        List.rev (!seen) = cs
                        andalso SS.foldl f "z" ss = List.foldl f "z" cs
                        andalso SS.foldr f "z" ss = List.foldr f "z" cs
                      end),

          P.forAll ("translate is concat of the mapped explosion",
                    windowed, showWindowed,
                    fn w =>
                      let val f = fn c => String.str c ^ "-"
                      in
                        SS.translate f (ssOf w)
                        = String.concat (List.map f (SS.explode (ssOf w)))
                      end),

          P.forAll ("tokens and fields agree with the String versions",
                    windowed, showWindowed,
                    fn w =>
                      let val str = SS.string (ssOf w)
                      in
                        List.map SS.string (SS.tokens comma (ssOf w))
                        = String.tokens comma str
                        andalso List.map SS.string (SS.fields comma (ssOf w))
                                = String.fields comma str
                      end),

          P.forAll ("extract with a length is substring", windowed, showWindowed,
                    fn (s, i, n) =>
                      SS.base (SS.extract (s, i, SOME n))
                      = SS.base (SS.substring (s, i, n))),

          P.forAll ("full is the whole-string window", str, showS,
                    fn s =>
                      SS.base (SS.full s)
                      = SS.base (SS.substring (s, 0, String.size s)))
        ])
      ])
  end
