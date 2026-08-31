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
                                         dst = dst, di = 3});
              A.raises "negative offset" A.isSubscript
                (fn () => Array.copyVec {src = Vector.fromList [1, 2],
                                         dst = dst, di = ~1})
            end),

          (* "In copy, if dst and src are equal, we must have di = 0 to avoid
           * an exception, and copy is then the identity." *)
          Case ("copying an array onto itself requires a zero offset", fn () =>
            let
              val a = Array.fromList [1, 2, 3]
            in
              A.noRaise "at offset zero"
                (fn () => Array.copy {src = a, dst = a, di = 0});
              A.eqIntList "and changes nothing" ([1, 2, 3], toList a);
              A.raises "at any other offset" A.isSubscript
                (fn () => Array.copy {src = a, dst = a, di = A.hide 1})
            end),

          Case ("copying an empty source is always legal", fn () =>
            let
              val dst = Array.fromList [1, 2, 3]
            in
              A.noRaise "at the far end"
                (fn () => Array.copy {src = Array.fromList ([] : int list),
                                      dst = dst, di = 3});
              A.eqIntList "and changes nothing" ([1, 2, 3], toList dst)
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

          Case ("find, findi, exists and all stop at the first decision",
            fn () =>
              let
                val a = Array.fromList [1, 2, 3, 4]
                fun counting p =
                  let val n = ref 0
                  in (n, fn x => (n := !n + 1; p x)) end
                val (x, px) = counting (fn v => v mod 2 = 0)
                val (y, py) = counting (fn v => v mod 2 = 0)
                val (z, pz) = counting (fn v => v mod 2 = 0)
              in
                A.eqIntOption "find" (SOME 2, Array.find px a);
                A.eqInt "find stopped" (2, !x);
                A.eqBool "exists" (true, Array.exists py a);
                A.eqInt "exists stopped" (2, !y);
                A.eqBool "all" (false, Array.all pz a);
                A.eqInt "all stopped" (1, !z)
              end),

          Case ("tabulate applies its function in increasing index order",
            fn () =>
              let
                val seen = ref []
                val a = Array.tabulate (4, fn i => (seen := i :: !seen; i))
              in
                A.eqIntList "the order of the calls" ([0, 1, 2, 3], List.rev (!seen));
                A.eqIntList "the result" ([0, 1, 2, 3], toList a)
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

          (* "the result is equivalent to
           *  Vector.tabulate (length arr, fn i => sub (arr, i))" *)
          P.forAll ("vector is the tabulation of the subscripts",
                    ints, Show.intList,
                    fn xs =>
                      let val a = Array.fromList xs
                      in
                        Array.vector a
                        = Vector.tabulate (Array.length a,
                                           fn i => Array.sub (a, i))
                      end),

          (* "The expression modify f arr is equivalent to
           *  modifyi (f o #2) arr." *)
          P.forAll ("modify is modifyi with the index dropped",
                    ints, Show.intList,
                    fn xs =>
                      let
                        val f = fn x => x * 3 + 1
                        val a = Array.fromList xs
                        val b = Array.fromList xs
                      in
                        Array.modify f a;
                        Array.modifyi (f o #2) b;
                        toList a = toList b
                      end),

          P.forAll ("modifyi sees every index in increasing order",
                    ints, Show.intList,
                    fn xs =>
                      let
                        val a = Array.fromList xs
                        val seen = ref []
                        val () = Array.modifyi (fn (i, x) => (seen := i :: !seen; x)) a
                      in
                        List.rev (!seen) = List.tabulate (List.length xs, fn i => i)
                        andalso toList a = xs
                      end),

          P.forAll ("appi and app visit in increasing index order",
                    ints, Show.intList,
                    fn xs =>
                      let
                        val a = Array.fromList xs
                        val seen = ref []
                        val () = Array.appi (fn (i, x) => seen := (i, x) :: !seen) a
                        val plain = ref []
                        val () = Array.app (fn x => plain := x :: !plain) a
                      in
                        List.rev (!seen)
                        = List.tabulate (List.length xs,
                                         fn i => (i, List.nth (xs, i)))
                        andalso List.rev (!plain) = xs
                      end),

          P.forAll ("foldl and foldr are the indexed folds with the index dropped",
                    ints, Show.intList,
                    fn xs =>
                      let
                        val a = Array.fromList xs
                        val f = fn (v, acc) => acc ^ Int.toString v
                      in
                        Array.foldl f "z" a
                        = Array.foldli (fn (_, v, acc) => f (v, acc)) "z" a
                        andalso Array.foldr f "z" a
                                = Array.foldri (fn (_, v, acc) => f (v, acc)) "z" a
                      end),

          P.forAll ("foldli and foldri see the indices in their two orders",
                    ints, Show.intList,
                    fn xs =>
                      let
                        val a = Array.fromList xs
                        val n = List.length xs
                      in
                        Array.foldli (fn (i, _, acc) => i :: acc) [] a
                        = List.rev (List.tabulate (n, fn i => i))
                        andalso Array.foldri (fn (i, _, acc) => i :: acc) [] a
                                = List.tabulate (n, fn i => i)
                      end),

          P.forAll ("findi reports the first index satisfying the predicate",
                    ints, Show.intList,
                    fn xs =>
                      let
                        val a = Array.fromList xs
                        val p = fn x => x > 0
                        fun search i =
                          if i >= List.length xs then NONE
                          else if p (List.nth (xs, i)) then SOME (i, List.nth (xs, i))
                          else search (i + 1)
                      in
                        Array.findi (fn (_, x) => p x) a = search 0
                      end),

          P.forAll ("all is the negation of exists over the negated predicate",
                    ints, Show.intList,
                    fn xs =>
                      let
                        val a = Array.fromList xs
                        val p = fn x => x > 0
                      in
                        Array.all p a = not (Array.exists (not o p) a)
                      end),

          (* "the i(th) element in src ... being copied to position di + i in
           * the destination array" *)
          P.forAll ("copy places the source at the destination offset",
                    G.bind ints (fn xs =>
                      G.map (fn k => (xs, k)) (G.int (0, 5))),
                    Show.pair (Show.intList, Show.int),
                    fn (xs, k) =>
                      let
                        val n = List.length xs
                        val src = Array.fromList xs
                        val dst = Array.array (n + k, 0)
                      in
                        Array.copy {src = src, dst = dst, di = k};
                        toList dst
                        = List.tabulate (k, fn _ => 0) @ xs
                      end),

          P.forAll ("copyVec places the source at the destination offset",
                    G.bind ints (fn xs =>
                      G.map (fn k => (xs, k)) (G.int (0, 5))),
                    Show.pair (Show.intList, Show.int),
                    fn (xs, k) =>
                      let
                        val n = List.length xs
                        val dst = Array.array (n + k, 0)
                      in
                        Array.copyVec {src = Vector.fromList xs, dst = dst, di = k};
                        toList dst = List.tabulate (k, fn _ => 0) @ xs
                      end),

          P.forAll ("collate agrees with List.collate",
                    G.pair (ints, ints), Show.pair (Show.intList, Show.intList),
                    fn (xs, ys) =>
                      Array.collate Int.compare
                        (Array.fromList xs, Array.fromList ys)
                      = List.collate Int.compare (xs, ys))
        ])
      ])
  end
