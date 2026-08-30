(* Tests for the required monomorphic sequence structures and Text.
 *
 * CharVector, CharArray, Word8Vector and their slices are separate
 * implementations in most systems -- frequently hand-written for speed --
 * rather than instances of the polymorphic Vector and Array, so they are
 * tested in their own right.  CharVector.vector is required to be string and
 * CharVector.elem to be char, and the tests rely on that sharing directly:
 * if it did not hold, this file would not compile.
 *)

functor MonoSeqTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure CV = CharVector
    structure CA = CharArray
    structure CVS = CharVectorSlice
    structure CAS = CharArraySlice
    structure W8V = Word8Vector
    structure W8A = Word8Array
    structure W8VS = Word8VectorSlice
    structure W8AS = Word8ArraySlice

    val str = G.printableString
    val showS = Show.string
    fun caList a = CA.foldr (op ::) [] a
    fun caString a = String.implode (caList a)
    val b = Word8.fromInt
    fun w8vInts v = List.map Word8.toInt (W8V.foldr (op ::) [] v)
    fun w8aInts a = List.map Word8.toInt (W8A.foldr (op ::) [] a)
    fun ofInts ns = W8V.fromList (List.map b ns)

    (* A string with a legal window on it. *)
    val windowed =
      G.bind str (fn s =>
        G.bind (G.int (0, String.size s)) (fn i =>
          G.map (fn n => (s, i, n)) (G.int (0, String.size s - i))))
    val showWindowed = Show.triple (showS, Show.int, Show.int)

    val suite = Group ("Monomorphic sequences",
      [ Group ("CharVector is the string type",
        [ (* These two equalities are required by the Basis, and the tests
           * below silently depend on them everywhere else. *)
          Case ("a CharVector is a string and its elements are chars", fn () =>
            let
              val v : CV.vector = "abc"
              val c : CV.elem = #"a"
            in
              A.eqString "used as a string" ("abc", v);
              A.eqChar "used as a char" (#"a", c)
            end),

          Case ("fromList, tabulate and length", fn () =>
            (A.eqString "fromList" ("abc", CV.fromList [#"a", #"b", #"c"]);
             A.eqString "tabulate"
               ("abc", CV.tabulate (3, fn i => Char.chr (Char.ord #"a" + i)));
             A.eqInt "length" (3, CV.length "abc");
             A.eqInt "empty" (0, CV.length "");
             A.raises "negative tabulate" A.isSize
               (fn () => CV.tabulate (A.hide ~1, fn _ => #"a"));
             A.that "maxLen is non-negative" (CV.maxLen >= 0))),

          Case ("sub and update", fn () =>
            (A.eqChar "sub" (#"b", CV.sub ("abc", 1));
             A.raises "sub past the end" A.isSubscript
               (fn () => CV.sub ("abc", A.hide 3));
             A.raises "sub negative" A.isSubscript
               (fn () => CV.sub ("abc", A.hide ~1));
             A.eqString "update returns a new vector"
               ("axc", CV.update ("abc", 1, #"x"));
             A.raises "update past the end" A.isSubscript
               (fn () => CV.update ("abc", A.hide 3, #"x")))),

          Case ("concat", fn () =>
            (A.eqString "several" ("abcd", CV.concat ["ab", "", "cd"]);
             A.eqString "none" ("", CV.concat []))),

          Case ("traversal", fn () =>
            let
              val seen = ref []
            in
              CV.app (fn c => seen := c :: !seen) "abc";
              A.eqCharList "app" ([#"c", #"b", #"a"], !seen);
              seen := [];
              CV.appi (fn (i, c) => seen := Char.chr (Char.ord c + i) :: !seen) "abc";
              A.eqCharList "appi sees indices" ([#"e", #"c", #"a"], !seen);
              A.eqString "map" ("ABC", CV.map Char.toUpper "abc");
              A.eqString "mapi"
                ("abc", CV.mapi (fn (_, c) => c) "abc");
              A.eqCharList "foldr rebuilds" ([#"a", #"b", #"c"], CV.foldr op:: [] "abc");
              A.eqCharList "foldl reverses" ([#"c", #"b", #"a"], CV.foldl op:: [] "abc");
              A.eqIntList "foldli indices"
                ([2, 1, 0], CV.foldli (fn (i, _, acc) => i :: acc) [] "abc");
              A.eqIntList "foldri indices"
                ([0, 1, 2], CV.foldri (fn (i, _, acc) => i :: acc) [] "abc")
            end),

          Case ("searching", fn () =>
            (A.eqCharOption "find" (SOME #"b", CV.find (fn c => c > #"a") "abc");
             A.eqCharOption "find misses" (NONE, CV.find (fn c => c > #"z") "abc");
             A.eqBy (op =, Show.option (Show.pair (Show.int, Show.char)))
               "findi" (SOME (1, #"b"), CV.findi (fn (_, c) => c > #"a") "abc");
             A.eqBool "exists" (true, CV.exists (fn c => c = #"b") "abc");
             A.eqBool "all" (true, CV.all (fn c => c < #"z") "abc");
             A.eqOrder "collate" (LESS, CV.collate Char.compare ("ab", "abc"))))
        ]),

        Group ("CharArray",
        [ Case ("array, fromList, tabulate", fn () =>
            (A.eqString "array fills" ("xxx", caString (CA.array (3, #"x")));
             A.eqString "fromList" ("abc", caString (CA.fromList [#"a", #"b", #"c"]));
             A.eqString "tabulate"
               ("abc", caString (CA.tabulate (3, fn i => Char.chr (97 + i))));
             A.raises "negative length" A.isSize
               (fn () => CA.array (A.hide ~1, #"x"));
             A.that "maxLen is non-negative" (CA.maxLen >= 0))),

          Case ("sub, update and vector", fn () =>
            let
              val a = CA.fromList [#"a", #"b", #"c"]
            in
              A.eqChar "sub" (#"b", CA.sub (a, 1));
              CA.update (a, 1, #"x");
              A.eqString "after update" ("axc", caString a);
              A.eqString "vector takes a snapshot" ("axc", CA.vector a);
              A.raises "sub past the end" A.isSubscript
                (fn () => CA.sub (a, A.hide 3));
              A.raises "sub negative" A.isSubscript
                (fn () => CA.sub (a, A.hide ~1));
              A.raises "update past the end" A.isSubscript
                (fn () => CA.update (a, A.hide 3, #"y"))
            end),

          Case ("copy and copyVec", fn () =>
            let
              val dst = CA.array (4, #"-")
            in
              CA.copy { src = CA.fromList [#"a", #"b"], dst = dst, di = 1 };
              A.eqString "copy" ("-ab-", caString dst);
              CA.copyVec { src = "z", dst = dst, di = 3 };
              A.eqString "copyVec" ("-abz", caString dst);
              A.raises "past the end" A.isSubscript
                (fn () => CA.copyVec { src = "zz", dst = dst, di = 3 })
            end),

          Case ("modify and modifyi", fn () =>
            let
              val a = CA.fromList [#"a", #"b", #"c"]
            in
              CA.modify Char.toUpper a;
              A.eqString "modify" ("ABC", caString a);
              CA.modifyi (fn (i, c) => if i = 1 then #"x" else c) a;
              A.eqString "modifyi" ("AxC", caString a)
            end),

          Case ("length and app", fn () =>
            let
              val a = CA.fromList [#"a", #"b", #"c"]
              val seen = ref []
            in
              A.eqInt "length" (3, CA.length a);
              A.eqInt "an empty array" (0, CA.length (CA.fromList []));
              CA.app (fn c => seen := c :: !seen) a;
              A.eqCharList "app visits in order" ([#"c", #"b", #"a"], !seen);
              seen := [];
              CA.appi (fn (i, c) => seen := Char.chr (Char.ord c + i) :: !seen) a;
              A.eqCharList "appi sees indices" ([#"e", #"c", #"a"], !seen)
            end),

          Case ("folds and searches", fn () =>
            let
              val a = CA.fromList [#"a", #"b", #"c"]
            in
              A.eqCharList "foldr" ([#"a", #"b", #"c"], CA.foldr op:: [] a);
              A.eqCharList "foldl" ([#"c", #"b", #"a"], CA.foldl op:: [] a);
              A.eqCharOption "find" (SOME #"b", CA.find (fn c => c > #"a") a);
              A.eqBool "exists" (true, CA.exists (fn c => c = #"c") a);
              A.eqBool "all" (true, CA.all (fn c => c >= #"a") a);
              A.eqOrder "collate" (EQUAL,
                CA.collate Char.compare (a, CA.fromList [#"a", #"b", #"c"]))
            end)
        ]),

        Group ("CharVectorSlice and CharArraySlice",
        [ Case ("slicing a string", fn () =>
            let
              val s = CVS.slice ("abcde", 1, SOME 3)
            in
              A.eqInt "length" (3, CVS.length s);
              A.eqString "vector" ("bcd", CVS.vector s);
              A.eqChar "sub is relative" (#"b", CVS.sub (s, 0));
              A.eqBool "not empty" (false, CVS.isEmpty s);
              A.eqBy (op =, Show.triple (Show.string, Show.int, Show.int))
                "base" (("abcde", 1, 3), CVS.base s);
              A.raises "past the window" A.isSubscript
                (fn () => CVS.sub (s, A.hide 3))
            end),

          Case ("full, subslice and concat", fn () =>
            (A.eqString "full" ("abc", CVS.vector (CVS.full "abc"));
             A.eqString "subslice"
               ("cd", CVS.vector (CVS.subslice (CVS.slice ("abcde", 1, SOME 3),
                                                1, SOME 2)));
             A.eqString "concat"
               ("bcd", CVS.concat [CVS.slice ("abc", 1, SOME 2),
                                   CVS.slice ("xdz", 1, SOME 1)]))),

          Case ("getItem and traversal", fn () =>
            let
              val s = CVS.slice ("abcde", 1, SOME 3)
            in
              case CVS.getItem s of
                  NONE => A.fail "expected an item"
                | SOME (c, rest) =>
                    (A.eqChar "head" (#"b", c);
                     A.eqString "rest" ("cd", CVS.vector rest));
              A.eqCharList "foldr" ([#"b", #"c", #"d"], CVS.foldr op:: [] s);
              A.eqString "map" ("BCD", CVS.map Char.toUpper s);
              A.eqIntList "foldli indices restart at zero"
                ([2, 1, 0], CVS.foldli (fn (i, _, acc) => i :: acc) [] s);
              A.eqCharOption "find" (SOME #"c", CVS.find (fn c => c > #"b") s);
              A.eqBool "exists" (true, CVS.exists (fn c => c = #"c") s);
              A.eqBool "all" (true, CVS.all (fn c => c > #"a") s);
              A.eqOrder "collate" (EQUAL,
                CVS.collate Char.compare (s, CVS.full "bcd"))
            end),

          Case ("an array slice writes through to its array", fn () =>
            let
              val a = CA.fromList [#"a", #"b", #"c", #"d", #"e"]
              val s = CAS.slice (a, 1, SOME 3)
            in
              CAS.update (s, 0, #"X");
              A.eqChar "seen through the slice" (#"X", CAS.sub (s, 0));
              A.eqString "seen in the array" ("aXcde", caString a);
              A.eqString "vector" ("Xcd", CAS.vector s);
              A.eqInt "length" (3, CAS.length s);
              A.eqBy (op =, Show.pair (Show.int, Show.int))
                "base reports the offset and length within the array"
                ((1, 3), let val (_, i, n) = CAS.base s in (i, n) end);
              A.raises "update past the window" A.isSubscript
                (fn () => CAS.update (s, A.hide 3, #"Y"))
            end),

          Case ("array slice copy and modify", fn () =>
            let
              val a = CA.fromList [#"a", #"b", #"c", #"d", #"e"]
              val dst = CA.array (4, #"-")
            in
              CAS.copy { src = CAS.slice (a, 1, SOME 2), dst = dst, di = 1 };
              A.eqString "copy" ("-bc-", caString dst);
              CAS.copyVec { src = CVS.full "z", dst = dst, di = 3 };
              A.eqString "copyVec" ("-bcz", caString dst);
              CAS.modify Char.toUpper (CAS.slice (a, 1, SOME 3));
              A.eqString "modify touches only the window" ("aBCDe", caString a);
              CAS.modifyi (fn (i, _) => Char.chr (48 + i)) (CAS.slice (a, 1, SOME 2));
              A.eqString "modifyi indices restart at zero" ("a01De", caString a)
            end),

          Case ("array slice getItem, folds and isEmpty", fn () =>
            let
              val a = CA.fromList [#"a", #"b", #"c"]
              val s = CAS.slice (a, 1, SOME 2)
            in
              A.eqBool "not empty" (false, CAS.isEmpty s);
              A.eqBool "empty" (true, CAS.isEmpty (CAS.slice (a, 1, SOME 0)));
              A.eqString "full" ("abc", CAS.vector (CAS.full a));
              A.eqCharList "foldr" ([#"b", #"c"], CAS.foldr op:: [] s);
              A.eqCharList "foldl" ([#"c", #"b"], CAS.foldl op:: [] s);
              A.eqIntList "foldli" ([1, 0], CAS.foldli (fn (i,_,acc) => i::acc) [] s);
              A.eqIntList "foldri" ([0, 1], CAS.foldri (fn (i,_,acc) => i::acc) [] s);
              A.eqCharOption "find" (SOME #"c", CAS.find (fn c => c > #"b") s);
              A.eqBool "exists" (true, CAS.exists (fn c => c = #"b") s);
              A.eqBool "all" (true, CAS.all (fn c => c > #"a") s);
              A.eqOrder "collate" (EQUAL, CAS.collate Char.compare (s, CAS.full
                (CA.fromList [#"b", #"c"])));
              case CAS.getItem s of
                  NONE => A.fail "expected an item"
                | SOME (c, rest) =>
                    (A.eqChar "head" (#"b", c);
                     A.eqInt "rest length" (1, CAS.length rest));
              let val seen = ref []
              in
                CAS.app (fn c => seen := c :: !seen) s;
                A.eqCharList "app" ([#"c", #"b"], !seen);
                seen := [];
                CAS.appi (fn (i, c) => seen := Char.chr (Char.ord c + i) :: !seen) s;
                A.eqCharList "appi" ([#"d", #"b"], !seen)
              end
            end)
        ]),

        Group ("Word8VectorSlice and Word8ArraySlice",
        [ Case ("slicing a byte vector", fn () =>
            let
              val v = ofInts [1, 2, 3, 4, 5]
              val s = W8VS.slice (v, 1, SOME 3)
            in
              A.eqInt "length" (3, W8VS.length s);
              A.eqIntList "vector" ([2, 3, 4], w8vInts (W8VS.vector s));
              A.eqInt "sub is relative" (2, Word8.toInt (W8VS.sub (s, 0)));
              A.eqBool "not empty" (false, W8VS.isEmpty s);
              A.eqIntList "full" ([1, 2, 3, 4, 5], w8vInts (W8VS.vector (W8VS.full v)));
              A.eqIntList "subslice"
                ([3, 4], w8vInts (W8VS.vector (W8VS.subslice (s, 1, SOME 2))));
              A.eqIntList "concat"
                ([2, 3, 4, 5],
                 w8vInts (W8VS.concat [s, W8VS.slice (ofInts [4, 5], 1, SOME 1)]));
              A.raises "past the window" A.isSubscript
                (fn () => W8VS.sub (s, A.hide 3))
            end),

          Case ("byte vector slice traversal", fn () =>
            let
              val s = W8VS.slice (ofInts [1, 2, 3, 4, 5], 1, SOME 3)
            in
              A.eqIntList "foldr" ([2, 3, 4],
                List.map Word8.toInt (W8VS.foldr op:: [] s));
              A.eqIntList "foldl" ([4, 3, 2],
                List.map Word8.toInt (W8VS.foldl op:: [] s));
              A.eqIntList "foldli indices"
                ([2, 1, 0], W8VS.foldli (fn (i, _, acc) => i :: acc) [] s);
              A.eqIntList "foldri indices"
                ([0, 1, 2], W8VS.foldri (fn (i, _, acc) => i :: acc) [] s);
              A.eqIntList "map"
                ([4, 6, 8], w8vInts (W8VS.map (fn w => w * b 2) s));
              A.eqBool "exists" (true, W8VS.exists (fn w => w = b 3) s);
              A.eqBool "all" (true, W8VS.all (fn w => Word8.< (w, b 9)) s);
              A.eqOrder "collate" (EQUAL,
                W8VS.collate Word8.compare (s, W8VS.full (ofInts [2, 3, 4])));
              case W8VS.getItem s of
                  NONE => A.fail "expected an item"
                | SOME (w, rest) =>
                    (A.eqInt "head" (2, Word8.toInt w);
                     A.eqInt "rest length" (2, W8VS.length rest))
            end),

          Case ("a byte array slice writes through", fn () =>
            let
              val a = W8A.fromList (List.map b [1, 2, 3, 4, 5])
              val s = W8AS.slice (a, 1, SOME 3)
            in
              W8AS.update (s, 0, b 99);
              A.eqInt "through the slice" (99, Word8.toInt (W8AS.sub (s, 0)));
              A.eqIntList "in the array" ([1, 99, 3, 4, 5], w8aInts a);
              A.eqIntList "vector" ([99, 3, 4], w8vInts (W8AS.vector s));
              A.eqInt "the array's length" (5, W8A.length a);
              A.eqInt "the slice's length" (3, W8AS.length s);
              W8AS.modify (fn w => w + b 1) s;
              A.eqIntList "modify touches only the window"
                ([1, 100, 4, 5, 5], w8aInts a);
              A.raises "update past the window" A.isSubscript
                (fn () => W8AS.update (s, A.hide 3, b 0))
            end),

          Case ("byte array slice copying", fn () =>
            let
              val dst = W8A.array (4, b 0)
            in
              W8AS.copy { src = W8AS.slice (W8A.fromList (List.map b [1,2,3]), 1, SOME 2),
                          dst = dst, di = 1 };
              A.eqIntList "copy" ([0, 2, 3, 0], w8aInts dst);
              W8AS.copyVec { src = W8VS.slice (ofInts [7, 8], 1, SOME 1),
                             dst = dst, di = 3 };
              A.eqIntList "copyVec" ([0, 2, 3, 8], w8aInts dst)
            end),

          Case ("byte array slice traversal", fn () =>
            let
              val a = W8A.fromList (List.map b [1, 2, 3])
              val s = W8AS.slice (a, 1, SOME 2)
            in
              A.eqBool "isEmpty" (false, W8AS.isEmpty s);
              A.eqIntList "full" ([1, 2, 3], w8aInts a);
              A.eqIntList "foldr" ([2, 3],
                List.map Word8.toInt (W8AS.foldr op:: [] s));
              A.eqIntList "foldli" ([1, 0],
                W8AS.foldli (fn (i, _, acc) => i :: acc) [] s);
              A.eqIntList "foldri" ([0, 1],
                W8AS.foldri (fn (i, _, acc) => i :: acc) [] s);
              A.eqBool "exists" (true, W8AS.exists (fn w => w = b 3) s);
              A.eqBool "all" (true, W8AS.all (fn w => Word8.> (w, b 0)) s);
              A.eqOrder "collate" (EQUAL,
                W8AS.collate Word8.compare (s, W8AS.full (W8A.fromList (List.map b [2,3]))));
              W8AS.modifyi (fn (i, _) => b i) s;
              A.eqIntList "modifyi" ([1, 0, 1], w8aInts a);
              let val seen = ref []
              in
                W8AS.app (fn w => seen := Word8.toInt w :: !seen) s;
                A.eqIntList "app" ([1, 0], !seen);
                seen := [];
                W8AS.appi (fn (i, w) => seen := (i + Word8.toInt w) :: !seen) s;
                A.eqIntList "appi" ([2, 0], !seen)
              end;
              case W8AS.getItem s of
                  NONE => A.fail "expected an item"
                | SOME (w, rest) =>
                    (A.eqInt "head" (0, Word8.toInt w);
                     A.eqInt "rest length" (1, W8AS.length rest))
            end)
        ]),

        Group ("Text",
        [ (* Text bundles the character structures and requires them to share
           * their types with the top-level ones.  Passing a value built by one
           * to a function from the other is the check. *)
          Case ("Text.Char is the top-level Char", fn () =>
            (A.eqInt "ord" (Char.ord #"a", Text.Char.ord #"a");
             A.eqChar "chr agrees" (Char.chr 98, Text.Char.chr 98))),

          Case ("Text.String is the top-level String", fn () =>
            (A.eqString "concatenation agrees"
               (String.concat ["a", "b"], Text.String.concat ["a", "b"]);
             A.eqInt "a Text.String value works with String.size"
               (3, String.size (Text.String.implode [#"a", #"b", #"c"])))),

          Case ("Text.Substring is the top-level Substring", fn () =>
            A.eqString "a Text substring works with the top-level Substring"
              ("bc", Substring.string (Text.Substring.substring ("abcd", 1, 2)))),

          Case ("Text.CharVector and Text.CharArray agree with the top level",
            fn () =>
              (A.eqString "CharVector.tabulate"
                 (CV.tabulate (3, fn _ => #"z"),
                  Text.CharVector.tabulate (3, fn _ => #"z"));
               A.eqString "an array built by Text works with CharArray"
                 ("xx", CA.vector (Text.CharArray.array (2, #"x"))))),

          Case ("Text.CharVectorSlice and Text.CharArraySlice agree", fn () =>
            (A.eqString "vector slice"
               ("bc", CVS.vector (Text.CharVectorSlice.slice ("abcd", 1, SOME 2)));
             A.eqString "array slice"
               ("bc",
                CAS.vector (Text.CharArraySlice.slice
                              (CA.fromList [#"a", #"b", #"c"], 1, SOME 2)))))
        ]),

        Group ("laws",
        [ P.forAll ("a CharVector is the string it came from", str, showS,
                    fn s => CV.fromList (String.explode s) = s),

          P.forAll ("CharVector.length is String.size", str, showS,
                    fn s => CV.length s = String.size s),

          P.forAll ("CharVector.map is String.map", str, showS,
                    fn s => CV.map Char.toUpper s = String.map Char.toUpper s),

          P.forAll ("CharVector.concat is String.concat",
                    G.list str, Show.list showS,
                    fn ss => CV.concat ss = String.concat ss),

          P.forAll ("a CharArray round trips through its vector", str, showS,
                    fn s => CA.vector (CA.tabulate (String.size s,
                                                    fn i => String.sub (s, i)))
                            = s),

          P.forAll ("CharArray.modify is String.map in place", str, showS,
                    fn s =>
                      let
                        val a = CA.tabulate (String.size s, fn i => String.sub (s, i))
                      in
                        CA.modify Char.toUpper a;
                        CA.vector a = String.map Char.toUpper s
                      end),

          P.forAll ("a char vector slice is the corresponding substring",
                    windowed, showWindowed,
                    fn (s, i, n) =>
                      CVS.vector (CVS.slice (s, i, SOME n))
                      = String.substring (s, i, n)),

          P.forAll ("a char array slice agrees with the vector slice",
                    windowed, showWindowed,
                    fn (s, i, n) =>
                      let
                        val a = CA.tabulate (String.size s, fn k => String.sub (s, k))
                      in
                        CAS.vector (CAS.slice (a, i, SOME n))
                        = CVS.vector (CVS.slice (s, i, SOME n))
                      end),

          P.forAll ("slicing to the end runs to the end", windowed, showWindowed,
                    fn (s, i, _) =>
                      CVS.vector (CVS.slice (s, i, NONE))
                      = String.extract (s, i, NONE)),

          P.forAll ("the pieces around a window reassemble",
                    windowed, showWindowed,
                    fn (s, i, n) =>
                      CVS.vector (CVS.slice (s, 0, SOME i))
                      ^ CVS.vector (CVS.slice (s, i, SOME n))
                      ^ CVS.vector (CVS.slice (s, i + n, NONE))
                      = s),

          P.forAll ("a byte vector slice agrees with the list of bytes",
                    G.bind (G.list (G.int (0, 255))) (fn ns =>
                      G.bind (G.int (0, List.length ns)) (fn i =>
                        G.map (fn n => (ns, i, n))
                              (G.int (0, List.length ns - i)))),
                    Show.triple (Show.intList, Show.int, Show.int),
                    fn (ns, i, n) =>
                      w8vInts (W8VS.vector (W8VS.slice (ofInts ns, i, SOME n)))
                      = List.take (List.drop (ns, i), n))
        ])
      ])
  end
