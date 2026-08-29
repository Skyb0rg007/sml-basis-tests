(* Tests for ListPair.
 *
 * Every operation comes in two flavours: the plain one truncates to the
 * shorter list, the "Eq" one raises UnequalLengths.  The pairs of tests below
 * are written so that the difference is what is being checked. *)

functor ListPairTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val ints = G.list G.smallInt
    val showInts = Show.intList
    val pairOfLists = G.pair (ints, ints)
    val showPairOfLists = Show.pair (showInts, showInts)

    (* Two lists of the same length, for the Eq variants. *)
    val sameLength =
      G.sized (fn n =>
        G.bind (G.int (0, n)) (fn k =>
          G.pair (G.listN k G.smallInt, G.listN k G.smallInt)))

    val showIntPairList = Show.list (Show.pair (Show.int, Show.int))

    val suite = Group ("ListPair",
      [ Group ("truncating operations",
        [ Case ("zip stops at the shorter list", fn () =>
            (A.eqBy (op =, showIntPairList) "left is shorter"
               ([(1, 4), (2, 5)], ListPair.zip ([1, 2], [4, 5, 6]));
             A.eqBy (op =, showIntPairList) "right is shorter"
               ([(1, 4)], ListPair.zip ([1, 2], [4]));
             A.eqBy (op =, showIntPairList) "empty"
               ([], ListPair.zip ([], [1, 2])))),

          Case ("unzip", fn () =>
            let
              val (xs, ys) = ListPair.unzip [(1, 4), (2, 5)]
            in
              A.eqIntList "firsts" ([1, 2], xs);
              A.eqIntList "seconds" ([4, 5], ys)
            end),

          Case ("map truncates", fn () =>
            A.eqIntList "sums" ([5, 7], ListPair.map op+ ([1, 2], [4, 5, 6]))),

          Case ("app truncates", fn () =>
            let
              val seen = ref []
            in
              ListPair.app (fn (a, b) => seen := (a + b) :: !seen)
                           ([1, 2], [4, 5, 6]);
              A.eqIntList "visits" ([7, 5], !seen)
            end),

          Case ("foldl and foldr", fn () =>
            (A.eqInt "foldl" (12,
               ListPair.foldl (fn (a, b, acc) => acc + a + b) 0
                              ([1, 2], [4, 5, 6]));
             A.eqInt "foldr" (12,
               ListPair.foldr (fn (a, b, acc) => acc + a + b) 0
                              ([1, 2], [4, 5, 6])))),

          Case ("all and exists over the common prefix", fn () =>
            (A.eqBool "all, differing tail ignored" (true,
               ListPair.all (fn (a, b) => a < b) ([1, 2], [4, 5, 0]));
             A.eqBool "exists" (true,
               ListPair.exists (fn (a, b) => a = b) ([1, 5], [4, 5]));
             A.eqBool "exists, none" (false,
               ListPair.exists (fn (a, b) => a = b) ([1, 2], [4, 5])))),

          Case ("allEq compares lengths too", fn () =>
            (A.eqBool "same length, all satisfy" (true,
               ListPair.allEq (fn (a, b) => a < b) ([1, 2], [4, 5]));
             A.eqBool "different lengths" (false,
               ListPair.allEq (fn (a, b) => a < b) ([1, 2], [4, 5, 6]))))
        ]),

        Group ("length-checked operations",
        [ Case ("zipEq accepts equal lengths", fn () =>
            A.eqBy (op =, showIntPairList) "zipped"
              ([(1, 4), (2, 5)], ListPair.zipEq ([1, 2], [4, 5]))),

          Case ("zipEq rejects unequal lengths", fn () =>
            (A.raises "left shorter" A.isUnequalLengths
               (fn () => ListPair.zipEq ([1], [4, 5]));
             A.raises "right shorter" A.isUnequalLengths
               (fn () => ListPair.zipEq ([1, 2], [4])))),

          Case ("mapEq", fn () =>
            (A.eqIntList "sums" ([5, 7], ListPair.mapEq op+ ([1, 2], [4, 5]));
             A.raises "unequal" A.isUnequalLengths
               (fn () => ListPair.mapEq op+ ([1, 2], [4])))),

          Case ("appEq", fn () =>
            A.raises "unequal" A.isUnequalLengths
              (fn () => ListPair.appEq (fn _ => ()) ([1, 2], [4]))),

          Case ("foldlEq and foldrEq", fn () =>
            (A.eqInt "foldlEq" (12,
               ListPair.foldlEq (fn (a, b, acc) => acc + a + b) 0
                                ([1, 2], [4, 5]));
             A.raises "foldlEq unequal" A.isUnequalLengths
               (fn () => ListPair.foldlEq (fn (a, b, acc) => acc + a + b) 0
                                          ([1, 2], [4]));
             A.raises "foldrEq unequal" A.isUnequalLengths
               (fn () => ListPair.foldrEq (fn (a, b, acc) => acc + a + b) 0
                                          ([1, 2], [4])))),

          (* LIST_PAIR has no existsEq: allEq is the only length-aware
           * predicate, and it reports a length mismatch by returning false
           * rather than by raising. *)
          Case ("allEq reports a length mismatch as false, not an exception",
            fn () =>
              (A.eqBool "unequal lengths" (false,
                 ListPair.allEq (fn _ => true) ([1, 2], [4]));
               A.noRaise "no exception escapes"
                 (fn () => ListPair.allEq (fn _ => true) ([1, 2], [4]))))
        ]),

        Group ("laws",
        [ P.forAll ("zip produces the shorter length",
                    pairOfLists, showPairOfLists,
                    fn (xs, ys) =>
                      List.length (ListPair.zip (xs, ys))
                      = Int.min (List.length xs, List.length ys)),

          P.forAll ("unzip inverts zip on equal lengths",
                    sameLength, showPairOfLists,
                    fn (xs, ys) => ListPair.unzip (ListPair.zip (xs, ys)) = (xs, ys)),

          P.forAll ("zip inverts unzip",
                    G.list (G.pair (G.smallInt, G.smallInt)), showIntPairList,
                    fn ps => ListPair.zip (ListPair.unzip ps) = ps),

          P.forAll ("zipEq agrees with zip when lengths match",
                    sameLength, showPairOfLists,
                    fn (xs, ys) => ListPair.zipEq (xs, ys) = ListPair.zip (xs, ys)),

          P.forAll ("map is zip then List.map",
                    pairOfLists, showPairOfLists,
                    fn (xs, ys) =>
                      ListPair.map op+ (xs, ys)
                      = List.map op+ (ListPair.zip (xs, ys))),

          P.forAll ("foldl over pairs matches folding the zip",
                    pairOfLists, showPairOfLists,
                    fn (xs, ys) =>
                      ListPair.foldl (fn (a, b, acc) => acc + a + b) 0 (xs, ys)
                      = List.foldl (fn ((a, b), acc) => acc + a + b) 0
                                   (ListPair.zip (xs, ys))),

          P.forAll ("all is the dual of exists",
                    pairOfLists, showPairOfLists,
                    fn (xs, ys) =>
                      ListPair.all (fn (a, b) => a < b) (xs, ys)
                      = not (ListPair.exists (fn (a, b) => a >= b) (xs, ys))),

          P.forAll ("allEq implies equal lengths",
                    pairOfLists, showPairOfLists,
                    fn (xs, ys) =>
                      P.implies (ListPair.allEq (fn _ => true) (xs, ys),
                                 List.length xs = List.length ys))
        ])
      ])
  end
