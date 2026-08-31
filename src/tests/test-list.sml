(* Tests for the List structure and the list operations in the top-level
 * environment. *)

functor ListTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val ints = G.list G.smallInt
    val ints1 = G.list1 G.smallInt
    val showInts = Show.intList

    (* A list paired with a legal index into it. *)
    val listAndIndex =
      G.bind ints1 (fn xs =>
        G.map (fn i => (xs, i)) (G.int (0, List.length xs - 1)))

    (* A list paired with a legal split point, 0 .. length inclusive. *)
    val listAndSplit =
      G.bind ints (fn xs =>
        G.map (fn k => (xs, k)) (G.int (0, List.length xs)))

    val showListAndInt = Show.pair (showInts, Show.int)

    val even = fn n => n mod 2 = 0

    val suite = Group ("List",
      [ Group ("basics",
        [ Case ("null", fn () =>
            (A.eqBool "empty" (true, List.null []);
             A.eqBool "non-empty" (false, List.null [1]))),

          Case ("length", fn () =>
            (A.eqInt "empty" (0, List.length ([] : int list));
             A.eqInt "three" (3, List.length [1, 2, 3]))),

          Case ("hd and tl", fn () =>
            (A.eqInt "hd" (1, List.hd [1, 2, 3]);
             A.eqIntList "tl" ([2, 3], List.tl [1, 2, 3]);
             A.raises "hd []" A.isEmpty (fn () => List.hd ([] : int list));
             A.raises "tl []" A.isEmpty (fn () => List.tl ([] : int list)))),

          Case ("last", fn () =>
            (A.eqInt "last" (3, List.last [1, 2, 3]);
             A.raises "last []" A.isEmpty (fn () => List.last ([] : int list)))),

          Case ("getItem", fn () =>
            (A.eqBy (op =, Show.option (Show.pair (Show.int, showInts)))
               "non-empty" (SOME (1, [2, 3]), List.getItem [1, 2, 3]);
             A.eqBy (op =, Show.option (Show.pair (Show.int, showInts)))
               "empty" (NONE, List.getItem ([] : int list)))),

          Case ("nth", fn () =>
            (A.eqInt "first" (1, List.nth ([1, 2, 3], 0));
             A.eqInt "last" (3, List.nth ([1, 2, 3], 2));
             A.raises "past the end" A.isSubscript
               (fn () => List.nth ([1, 2, 3], A.hide 3));
             A.raises "negative" A.isSubscript
               (fn () => List.nth ([1, 2, 3], A.hide ~1)))),

          Case ("take", fn () =>
            (A.eqIntList "none" ([], List.take ([1, 2, 3], 0));
             A.eqIntList "some" ([1, 2], List.take ([1, 2, 3], 2));
             A.eqIntList "all" ([1, 2, 3], List.take ([1, 2, 3], 3));
             A.raises "too many" A.isSubscript
               (fn () => List.take ([1, 2, 3], A.hide 4));
             A.raises "negative" A.isSubscript
               (fn () => List.take ([1, 2, 3], A.hide ~1)))),

          Case ("drop", fn () =>
            (A.eqIntList "none" ([1, 2, 3], List.drop ([1, 2, 3], 0));
             A.eqIntList "some" ([3], List.drop ([1, 2, 3], 2));
             A.eqIntList "all" ([], List.drop ([1, 2, 3], 3));
             A.raises "too many" A.isSubscript
               (fn () => List.drop ([1, 2, 3], A.hide 4));
             A.raises "negative" A.isSubscript
               (fn () => List.drop ([1, 2, 3], A.hide ~1)))),

          Case ("rev", fn () =>
            (A.eqIntList "empty" ([], List.rev ([] : int list));
             A.eqIntList "three" ([3, 2, 1], List.rev [1, 2, 3]))),

          Case ("append", fn () =>
            (A.eqIntList "both non-empty" ([1, 2, 3, 4], [1, 2] @ [3, 4]);
             A.eqIntList "left empty" ([3, 4], [] @ [3, 4]);
             A.eqIntList "right empty" ([1, 2], [1, 2] @ []))),

          Case ("revAppend", fn () =>
            A.eqIntList "revAppend" ([2, 1, 3, 4], List.revAppend ([1, 2], [3, 4]))),

          Case ("concat", fn () =>
            (A.eqIntList "nested" ([1, 2, 3], List.concat [[1], [], [2, 3]]);
             A.eqIntList "empty" ([], List.concat ([] : int list list)))),

          Case ("tabulate", fn () =>
            (A.eqIntList "squares" ([0, 1, 4], List.tabulate (3, fn i => i * i));
             A.eqIntList "zero" ([], List.tabulate (0, fn i => i));
             A.raises "negative" A.isSize
               (fn () => List.tabulate (A.hide ~1, fn i => i))))
        ]),

        Group ("traversal",
        [ Case ("app visits left to right", fn () =>
            let
              val seen = ref []
            in
              List.app (fn n => seen := n :: !seen) [1, 2, 3];
              A.eqIntList "reversed order of visits" ([3, 2, 1], !seen)
            end),

          Case ("map", fn () =>
            A.eqIntList "doubled" ([2, 4, 6], List.map (fn n => n * 2) [1, 2, 3])),

          Case ("mapPartial", fn () =>
            A.eqIntList "evens doubled" ([4, 8],
              List.mapPartial (fn n => if even n then SOME (n * 2) else NONE)
                              [1, 2, 3, 4])),

          Case ("find", fn () =>
            (A.eqIntOption "found" (SOME 2, List.find even [1, 2, 3]);
             A.eqIntOption "not found" (NONE, List.find even [1, 3]))),

          Case ("filter", fn () =>
            A.eqIntList "evens" ([2, 4], List.filter even [1, 2, 3, 4])),

          Case ("partition", fn () =>
            let
              val (yes, no) = List.partition even [1, 2, 3, 4]
            in
              A.eqIntList "satisfying" ([2, 4], yes);
              A.eqIntList "not satisfying" ([1, 3], no)
            end),

          Case ("foldl associates to the left", fn () =>
            (A.eqInt "sum" (6, List.foldl op+ 0 [1, 2, 3]);
             A.eqIntList "cons builds the reverse"
               ([3, 2, 1], List.foldl op:: [] [1, 2, 3]);
             A.eqString "order of combination"
               ("(((z)1)2)3",
                List.foldl (fn (n, acc) => "(" ^ acc ^ ")" ^ Int.toString n)
                           "z" [1, 2, 3]))),

          Case ("foldr associates to the right", fn () =>
            (A.eqInt "sum" (6, List.foldr op+ 0 [1, 2, 3]);
             A.eqIntList "cons rebuilds the list"
               ([1, 2, 3], List.foldr op:: [] [1, 2, 3]))),

          Case ("exists and all", fn () =>
            (A.eqBool "exists hit" (true, List.exists even [1, 2, 3]);
             A.eqBool "exists miss" (false, List.exists even [1, 3]);
             A.eqBool "exists on empty" (false, List.exists even []);
             A.eqBool "all hit" (true, List.all even [2, 4]);
             A.eqBool "all miss" (false, List.all even [2, 3]);
             A.eqBool "all on empty" (true, List.all even []))),

          (* "applies f to each element x of the list l, from left to right,
           * until f x evaluates to true" -- so the traversal stops at the
           * first decisive element. *)
          Case ("find, exists and all stop at the first decisive element",
            fn () =>
              let
                fun counting p =
                  let val n = ref 0
                  in (n, fn x => (n := !n + 1; p x)) end
                val (fnd, pf) = counting even
                val (exs, pe) = counting even
                val (alls, pa) = counting even
              in
                A.eqIntOption "find" (SOME 2, List.find pf [1, 2, 3, 4]);
                A.eqInt "find stopped after the hit" (2, !fnd);
                A.eqBool "exists" (true, List.exists pe [1, 2, 3, 4]);
                A.eqInt "exists stopped after the hit" (2, !exs);
                A.eqBool "all" (false, List.all pa [2, 3, 4]);
                A.eqInt "all stopped after the miss" (2, !alls)
              end),

          Case ("map, mapPartial, filter and partition go left to right",
            fn () =>
              let
                fun recording () =
                  let val seen = ref []
                  in (seen, fn x => (seen := x :: !seen; x)) end
                val (m, fm) = recording ()
                val (mp, fmp) = recording ()
                val (fl, ffl) = recording ()
                val (pt, fpt) = recording ()
              in
                ignore (List.map fm [1, 2, 3]);
                A.eqIntList "map" ([3, 2, 1], !m);
                ignore (List.mapPartial (fn x => SOME (fmp x)) [1, 2, 3]);
                A.eqIntList "mapPartial" ([3, 2, 1], !mp);
                ignore (List.filter (fn x => even (ffl x)) [1, 2, 3]);
                A.eqIntList "filter" ([3, 2, 1], !fl);
                ignore (List.partition (fn x => even (fpt x)) [1, 2, 3]);
                A.eqIntList "partition" ([3, 2, 1], !pt)
              end),

          Case ("collate", fn () =>
            (A.eqOrder "equal" (EQUAL, List.collate Int.compare ([1, 2], [1, 2]));
             A.eqOrder "prefix is less"
               (LESS, List.collate Int.compare ([1], [1, 2]));
             A.eqOrder "longer is greater"
               (GREATER, List.collate Int.compare ([1, 2], [1]));
             A.eqOrder "first difference wins"
               (LESS, List.collate Int.compare ([1, 0], [1, 2]));
             A.eqOrder "empty against empty"
               (EQUAL, List.collate Int.compare ([], []))))
        ]),

        Group ("laws",
        [ P.forAll ("rev is an involution", ints, showInts,
                    fn xs => List.rev (List.rev xs) = xs),

          P.forAll ("length is additive over append",
                    G.pair (ints, ints), Show.pair (showInts, showInts),
                    fn (xs, ys) =>
                      List.length (xs @ ys) = List.length xs + List.length ys),

          P.forAll ("rev distributes over append, swapping sides",
                    G.pair (ints, ints), Show.pair (showInts, showInts),
                    fn (xs, ys) =>
                      List.rev (xs @ ys) = List.rev ys @ List.rev xs),

          P.forAll ("append is associative",
                    G.triple (ints, ints, ints),
                    Show.triple (showInts, showInts, showInts),
                    fn (xs, ys, zs) => (xs @ ys) @ zs = xs @ (ys @ zs)),

          P.forAll ("the empty list is a unit for append", ints, showInts,
                    fn xs => [] @ xs = xs andalso xs @ [] = xs),

          P.forAll ("foldl with cons reverses", ints, showInts,
                    fn xs => List.foldl op:: [] xs = List.rev xs),

          P.forAll ("foldr with cons is the identity", ints, showInts,
                    fn xs => List.foldr op:: [] xs = xs),

          P.forAll ("foldl on the reverse equals foldr", ints, showInts,
                    fn xs =>
                      List.foldl op+ 0 xs = List.foldr op+ 0 (List.rev xs)),

          P.forAll ("map fuses", ints, showInts,
                    fn xs =>
                      let
                        val f = fn n => n + 1
                        val g = fn n => n * 2
                      in
                        List.map f (List.map g xs) = List.map (f o g) xs
                      end),

          P.forAll ("map preserves length", ints, showInts,
                    fn xs => List.length (List.map (fn n => n * 3) xs)
                             = List.length xs),

          P.forAll ("revAppend is rev then append",
                    G.pair (ints, ints), Show.pair (showInts, showInts),
                    fn (xs, ys) => List.revAppend (xs, ys) = List.rev xs @ ys),

          P.forAll ("concat of singletons is the identity", ints, showInts,
                    fn xs => List.concat (List.map (fn x => [x]) xs) = xs),

          P.forAll ("concat is additive over lengths",
                    G.list ints, Show.list showInts,
                    fn xss =>
                      List.length (List.concat xss)
                      = List.foldl (fn (xs, a) => a + List.length xs) 0 xss),

          P.forAll ("partition splits into filter and its complement",
                    ints, showInts,
                    fn xs =>
                      List.partition even xs
                      = (List.filter even xs,
                         List.filter (not o even) xs)),

          P.forAll ("filter preserves relative order and membership",
                    ints, showInts,
                    fn xs =>
                      List.filter even xs
                      = List.mapPartial (fn n => if even n then SOME n else NONE) xs),

          P.forAll ("take and drop reassemble the list",
                    listAndSplit, showListAndInt,
                    fn (xs, k) => List.take (xs, k) @ List.drop (xs, k) = xs),

          P.forAll ("take yields exactly k elements",
                    listAndSplit, showListAndInt,
                    fn (xs, k) => List.length (List.take (xs, k)) = k),

          P.forAll ("nth is the head of the corresponding drop",
                    listAndIndex, showListAndInt,
                    fn (xs, i) => List.nth (xs, i) = List.hd (List.drop (xs, i))),

          P.forAll ("last is the head of the reverse", ints1, showInts,
                    fn xs => List.last xs = List.hd (List.rev xs)),

          P.forAll ("exists is the dual of all", ints, showInts,
                    fn xs => List.exists even xs = not (List.all (not o even) xs)),

          P.forAll ("find agrees with filter", ints, showInts,
                    fn xs =>
                      List.find even xs
                      = (case List.filter even xs of [] => NONE | y :: _ => SOME y)),

          P.forAll ("tabulate has the requested length", G.int (0, 30), Show.int,
                    fn n => List.length (List.tabulate (n, fn i => i)) = n),

          P.forAll ("tabulate applies the function at each index",
                    G.int (0, 30), Show.int,
                    fn n =>
                      List.tabulate (n, fn i => i * i)
                      = List.map (fn i => i * i) (List.tabulate (n, fn i => i))),

          P.forAll ("collate on identical lists is EQUAL", ints, showInts,
                    fn xs => List.collate Int.compare (xs, xs) = EQUAL),

          P.forAll ("collate is antisymmetric",
                    G.pair (ints, ints), Show.pair (showInts, showInts),
                    fn (xs, ys) =>
                      let
                        fun flip LESS = GREATER
                          | flip GREATER = LESS
                          | flip EQUAL = EQUAL
                      in
                        List.collate Int.compare (xs, ys)
                        = flip (List.collate Int.compare (ys, xs))
                      end),

          P.forAll ("a proper prefix collates as LESS",
                    G.pair (ints, ints1), Show.pair (showInts, showInts),
                    fn (xs, ys) => List.collate Int.compare (xs, xs @ ys) = LESS),

          (* "The above expression is equivalent to:
           *  ((map valOf) o (filter isSome) o (map f)) l" *)
          P.forAll ("mapPartial is map, filter isSome, map valOf",
                    ints, showInts,
                    fn xs =>
                      let
                        val f = fn n => if even n then SOME (n * 2) else NONE
                      in
                        List.mapPartial f xs
                        = ((List.map valOf) o (List.filter isSome)
                           o (List.map f)) xs
                      end),

          (* "concat[l1,l2,...ln] = l1 @ l2 @ ... @ ln" *)
          P.forAll ("concat is a fold of append",
                    G.list ints, Show.list showInts,
                    fn xss => List.concat xss = List.foldr (op @) [] xss),

          (* "foldl f init [x1, x2, ..., xn] returns
           *  f(xn,...,f(x2, f(x1, init))...)", and the dual for foldr.  The
           * combining operator is non-commutative so that the nesting is
           * observable, and the comparison is against the recursion the
           * specification writes out rather than against another fold. *)
          P.forAll ("foldl nests as the specification writes it",
                    ints, showInts,
                    fn xs =>
                      let
                        val f = fn (x, a) => "(" ^ a ^ ")" ^ Int.toString x
                        fun spec (a, []) = a
                          | spec (a, x :: rest) = spec (f (x, a), rest)
                      in
                        List.foldl f "z" xs = spec ("z", xs)
                      end),

          P.forAll ("foldr nests as the specification writes it",
                    ints, showInts,
                    fn xs =>
                      let
                        val f = fn (x, a) => "(" ^ a ^ ")" ^ Int.toString x
                        fun spec (a, []) = a
                          | spec (a, x :: rest) = f (x, spec (a, rest))
                      in
                        List.foldr f "z" xs = spec ("z", xs)
                      end),

          P.forAll ("app visits every element from left to right",
                    ints, showInts,
                    fn xs =>
                      let
                        val seen = ref []
                        val () = List.app (fn x => seen := x :: !seen) xs
                      in
                        List.rev (!seen) = xs
                      end),

          P.forAll ("take of the whole list is the list, drop of it is empty",
                    ints, showInts,
                    fn xs =>
                      List.take (xs, List.length xs) = xs
                      andalso List.drop (xs, List.length xs) = []),

          P.forAll ("nth at zero is hd", ints1, showInts,
                    fn xs => List.nth (xs, 0) = List.hd xs),

          P.forAll ("null and length agree", ints, showInts,
                    fn xs => List.null xs = (List.length xs = 0)),

          P.forAll ("length counts the elements", ints, showInts,
                    fn xs => List.length xs = List.foldl (fn (_, a) => a + 1) 0 xs),

          P.forAll ("getItem agrees with hd and tl", ints, showInts,
                    fn xs =>
                      List.getItem xs
                      = (case xs of [] => NONE | y :: ys => SOME (y, ys)))
        ])
      ])
  end
