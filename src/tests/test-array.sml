(* Tests for the Array structure.
 *
 * Arrays are mutable, so most of these tests are about what changed and what
 * did not.  Array equality is identity, not content, and that is checked
 * explicitly rather than assumed.
 *)

functor ArrayTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    fun toList a = Array.foldr (op ::) [] a
    fun fromList xs = Array.fromList xs
    val showA = Show.intList
    fun showArr a = Show.intList (toList a)

    val ints = G.list G.smallInt
    val arr = G.map Array.fromList ints

    val arrAndIndex =
      G.bind (G.filter (fn xs => not (List.null xs)) ints) (fn xs =>
        G.map (fn i => (xs, i)) (G.int (0, List.length xs - 1)))
    val showListAndIndex = Show.pair (Show.intList, Show.int)

    val suite = Group ("Array",
      [ Group ("construction",
        [ Case ("array fills with the initial value", fn () =>
            (A.eqIntList "three sevens" ([7, 7, 7], toList (Array.array (3, 7)));
             A.eqInt "zero length" (0, Array.length (Array.array (0, 7)));
             A.raises "negative length" A.isSize (fn () => Array.array (A.hide ~1, A.hide 7)))),

          Case ("fromList and tabulate", fn () =>
            (A.eqIntList "fromList" ([1, 2, 3], toList (Array.fromList [1, 2, 3]));
             A.eqIntList "tabulate"
               ([0, 1, 4], toList (Array.tabulate (3, fn i => i * i)));
             A.raises "negative tabulate" A.isSize
               (fn () => Array.tabulate (A.hide ~1, fn i => i)))),

          Case ("maxLen is non-negative", fn () =>
            A.that "maxLen >= 0" (Array.maxLen >= 0)),

          Case ("arrays are compared by identity, not by content", fn () =>
            let
              val a = Array.fromList [1, 2, 3]
              val b = Array.fromList [1, 2, 3]
            in
              A.that "an array is equal to itself" (a = a);
              A.that "distinct arrays with equal contents differ" (a <> b)
            end)
        ]),

        Group ("access and mutation",
        [ Case ("sub and update", fn () =>
            let
              val a = Array.fromList [1, 2, 3]
            in
              A.eqInt "sub" (2, Array.sub (a, 1));
              Array.update (a, 1, 9);
              A.eqInt "after update" (9, Array.sub (a, 1));
              A.eqIntList "the rest is untouched" ([1, 9, 3], toList a);
              A.raises "sub past the end" A.isSubscript (fn () => Array.sub (a, A.hide 3));
              A.raises "sub negative" A.isSubscript (fn () => Array.sub (a, A.hide ~1));
              A.raises "update past the end" A.isSubscript
                (fn () => Array.update (a, A.hide 3, A.hide 0));
              A.raises "update negative" A.isSubscript
                (fn () => Array.update (a, A.hide ~1, A.hide 0))
            end),

          Case ("vector takes a snapshot", fn () =>
            let
              val a = Array.fromList [1, 2, 3]
              val v = Array.vector a
            in
              A.eqIntList "contents" ([1, 2, 3], Vector.foldr (op ::) [] v);
              Array.update (a, 0, 99);
              A.eqIntList "the snapshot does not follow the array"
                ([1, 2, 3], Vector.foldr (op ::) [] v)
            end)
        ]),

        Group ("copying",
        [ Case ("copy between distinct arrays", fn () =>
            let
              val src = Array.fromList [1, 2]
              val dst = Array.fromList [0, 0, 0, 0]
            in
              Array.copy {src = src, dst = dst, di = 1};
              A.eqIntList "copied into place" ([0, 1, 2, 0], toList dst)
            end),

          Case ("copy rejects a destination that is too small", fn () =>
            let
              val src = Array.fromList [1, 2, 3]
              val dst = Array.fromList [0, 0, 0]
            in
              A.raises "offset pushes past the end" A.isSubscript
                (fn () => Array.copy {src = src, dst = dst, di = 1});
              A.raises "negative offset" A.isSubscript
                (fn () => Array.copy {src = src, dst = dst, di = ~1})
            end),

          (* Overlapping copy within one array must behave as if the source
           * were read in full before anything was written. *)
          Case ("copy within a single array overlaps correctly", fn () =>
            let
              val a = Array.fromList [1, 2, 3, 4, 5]
            in
              Array.copy {src = a, dst = a, di = 0};
              A.eqIntList "copying onto itself changes nothing"
                ([1, 2, 3, 4, 5], toList a)
            end),

          Case ("copyVec", fn () =>
            let
              val dst = Array.fromList [0, 0, 0, 0]
            in
              Array.copyVec {src = Vector.fromList [1, 2], dst = dst, di = 2};
              A.eqIntList "copied" ([0, 0, 1, 2], toList dst);
              A.raises "past the end" A.isSubscript
                (fn () => Array.copyVec {src = Vector.fromList [1, 2],
                                         dst = dst, di = 3})
            end)
        ]),

        Group ("traversal",
        [ Case ("app and appi", fn () =>
            let
              val seen = ref []
              val a = Array.fromList [10, 20, 30]
            in
              Array.app (fn x => seen := x :: !seen) a;
              A.eqIntList "app" ([30, 20, 10], !seen);
              seen := [];
              Array.appi (fn (i, x) => seen := (i + x) :: !seen) a;
              A.eqIntList "appi" ([32, 21, 10], !seen)
            end),

          Case ("modify and modifyi mutate in place", fn () =>
            let
              val a = Array.fromList [1, 2, 3]
            in
              Array.modify (fn x => x * 2) a;
              A.eqIntList "modify" ([2, 4, 6], toList a);
              Array.modifyi (fn (i, x) => x + i) a;
              A.eqIntList "modifyi" ([2, 5, 8], toList a)
            end),

          Case ("folds", fn () =>
            let
              val a = Array.fromList [1, 2, 3]
            in
              A.eqInt "foldl" (6, Array.foldl op+ 0 a);
              A.eqIntList "foldl reverses" ([3, 2, 1], Array.foldl op:: [] a);
              A.eqIntList "foldr keeps order" ([1, 2, 3], Array.foldr op:: [] a);
              A.eqIntList "foldli indices"
                ([2, 1, 0], Array.foldli (fn (i, _, acc) => i :: acc) [] a);
              A.eqIntList "foldri indices"
                ([0, 1, 2], Array.foldri (fn (i, _, acc) => i :: acc) [] a)
            end),

          Case ("find, findi, exists, all", fn () =>
            let
              val a = Array.fromList [1, 2, 3, 4]
            in
              A.eqIntOption "find" (SOME 2, Array.find (fn x => x mod 2 = 0) a);
              A.eqBy (op =, Show.option (Show.pair (Show.int, Show.int)))
                "findi" (SOME (1, 2), Array.findi (fn (_, x) => x mod 2 = 0) a);
              A.eqBool "exists" (true, Array.exists (fn x => x = 3) a);
              A.eqBool "all" (true, Array.all (fn x => x > 0) a)
            end),

          Case ("collate", fn () =>
            A.eqOrder "prefix is less" (LESS,
              Array.collate Int.compare
                (Array.fromList [1], Array.fromList [1, 2])))
        ]),

        Group ("laws",
        [ P.forAll ("fromList and the fold are inverse", ints, Show.intList,
                    fn xs => toList (Array.fromList xs) = xs),

          P.forAll ("length agrees with the list", ints, Show.intList,
                    fn xs => Array.length (Array.fromList xs) = List.length xs),

          P.forAll ("array fills every position", G.int (0, 30), Show.int,
                    fn n => toList (Array.array (n, 7))
                            = List.tabulate (n, fn _ => 7)),

          P.forAll ("tabulate agrees with List.tabulate", G.int (0, 30), Show.int,
                    fn n =>
                      toList (Array.tabulate (n, fn i => i * 2))
                      = List.tabulate (n, fn i => i * 2)),

          P.forAll ("sub after update returns what was written",
                    arrAndIndex, showListAndIndex,
                    fn (xs, i) =>
                      let
                        val a = Array.fromList xs
                      in
                        Array.update (a, i, 999);
                        Array.sub (a, i) = 999
                      end),

          P.forAll ("update leaves every other position alone",
                    arrAndIndex, showListAndIndex,
                    fn (xs, i) =>
                      let
                        val a = Array.fromList xs
                        val () = Array.update (a, i, 999)
                      in
                        Array.foldli
                          (fn (j, x, acc) =>
                             acc andalso (j = i orelse x = List.nth (xs, j)))
                          true a
                      end),

          P.forAll ("vector then fromList round trips the contents",
                    ints, Show.intList,
                    fn xs =>
                      Vector.foldr (op ::) [] (Array.vector (Array.fromList xs))
                      = xs),

          P.forAll ("modify is map in place", ints, Show.intList,
                    fn xs =>
                      let
                        val a = Array.fromList xs
                      in
                        Array.modify (fn x => x * 3) a;
                        toList a = List.map (fn x => x * 3) xs
                      end),

          P.forAll ("copying an array onto a fresh one preserves it",
                    ints, Show.intList,
                    fn xs =>
                      let
                        val src = Array.fromList xs
                        val dst = Array.array (List.length xs, 0)
                      in
                        Array.copy {src = src, dst = dst, di = 0};
                        toList dst = xs
                      end),

          P.forAll ("foldr with cons rebuilds the list", ints, Show.intList,
                    fn xs => Array.foldr op:: [] (Array.fromList xs) = xs),

          P.forAll ("foldl with cons reverses", ints, Show.intList,
                    fn xs =>
                      Array.foldl op:: [] (Array.fromList xs) = List.rev xs),

          P.forAll ("collate agrees with List.collate",
                    G.pair (ints, ints), Show.pair (Show.intList, Show.intList),
                    fn (xs, ys) =>
                      Array.collate Int.compare
                        (Array.fromList xs, Array.fromList ys)
                      = List.collate Int.compare (xs, ys))
        ])
      ])
  end
