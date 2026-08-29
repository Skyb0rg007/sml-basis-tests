(* Tests for the Vector structure. *)

functor VectorTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val showV = Show.vector Show.int
    val eqV = A.eqBy (op =, showV)
    val vec = G.vector G.smallInt
    val ints = G.list G.smallInt

    fun toList v = Vector.foldr (op ::) [] v

    val vecAndIndex =
      G.bind (G.filter (fn v => Vector.length v > 0) vec) (fn v =>
        G.map (fn i => (v, i)) (G.int (0, Vector.length v - 1)))
    val showVecAndIndex = Show.pair (showV, Show.int)

    val suite = Group ("Vector",
      [ Group ("construction",
        [ Case ("fromList", fn () =>
            (A.eqIntList "round trip" ([1, 2, 3], toList (Vector.fromList [1, 2, 3]));
             A.eqInt "length" (3, Vector.length (Vector.fromList [1, 2, 3]));
             A.eqInt "empty" (0, Vector.length (Vector.fromList ([] : int list))))),

          Case ("tabulate", fn () =>
            (A.eqIntList "squares"
               ([0, 1, 4], toList (Vector.tabulate (3, fn i => i * i)));
             A.eqInt "zero length" (0, Vector.length (Vector.tabulate (0, fn i => i)));
             A.raises "negative length" A.isSize
               (fn () => Vector.tabulate (A.hide ~1, fn i => i)))),

          Case ("maxLen is non-negative", fn () =>
            A.that "maxLen >= 0" (Vector.maxLen >= 0)),

          Case ("concat", fn () =>
            (A.eqIntList "several"
               ([1, 2, 3],
                toList (Vector.concat [Vector.fromList [1],
                                       Vector.fromList [],
                                       Vector.fromList [2, 3]]));
             A.eqInt "nothing" (0, Vector.length (Vector.concat ([] : int vector list)))))
        ]),

        Group ("access",
        [ Case ("sub", fn () =>
            let
              (* Opaque so the out-of-range calls below really happen at run
               * time rather than being folded away; see Assert.opaque. *)
              val v = Vector.fromList [1, 2, 3]
              val empty = Vector.fromList ([] : int list)
            in
              A.eqInt "first" (1, Vector.sub (v, 0));
              A.eqInt "last" (3, Vector.sub (v, 2));
              A.raises "past the end" A.isSubscript (fn () => Vector.sub (v, A.hide 3));
              A.raises "negative" A.isSubscript (fn () => Vector.sub (v, A.hide ~1));
              A.raises "into an empty vector" A.isSubscript
                (fn () => Vector.sub (empty, A.hide 0))
            end),

          Case ("update returns a new vector and leaves the old one alone",
            fn () =>
              let
                val v = Vector.fromList [1, 2, 3]
                val v' = Vector.update (v, 1, 9)
              in
                A.eqIntList "updated" ([1, 9, 3], toList v');
                A.eqIntList "original is unchanged" ([1, 2, 3], toList v);
                A.raises "past the end" A.isSubscript
                  (fn () => Vector.update (v, A.hide 3, A.hide 9));
                A.raises "negative" A.isSubscript
                  (fn () => Vector.update (v, A.hide ~1, A.hide 9))
              end)
        ]),

        Group ("traversal",
        [ Case ("app and appi visit in order", fn () =>
            let
              val seen = ref []
              val seenI = ref []
              val v = Vector.fromList [10, 20, 30]
            in
              Vector.app (fn x => seen := x :: !seen) v;
              A.eqIntList "app" ([30, 20, 10], !seen);
              Vector.appi (fn (i, x) => seenI := (i + x) :: !seenI) v;
              A.eqIntList "appi sees the indices" ([32, 21, 10], !seenI)
            end),

          Case ("map and mapi", fn () =>
            (A.eqIntList "map"
               ([2, 4, 6], toList (Vector.map (fn x => x * 2)
                                              (Vector.fromList [1, 2, 3])));
             A.eqIntList "mapi"
               ([0, 2, 6], toList (Vector.mapi (fn (i, x) => i * x)
                                               (Vector.fromList [1, 2, 3]))))),

          Case ("foldl and foldr", fn () =>
            let
              val v = Vector.fromList [1, 2, 3]
            in
              A.eqInt "foldl sum" (6, Vector.foldl op+ 0 v);
              A.eqIntList "foldl builds the reverse"
                ([3, 2, 1], Vector.foldl op:: [] v);
              A.eqIntList "foldr keeps the order"
                ([1, 2, 3], Vector.foldr op:: [] v)
            end),

          Case ("foldli and foldri see the indices", fn () =>
            let
              val v = Vector.fromList [10, 20, 30]
            in
              A.eqIntList "foldli"
                ([2, 1, 0], Vector.foldli (fn (i, _, acc) => i :: acc) [] v);
              A.eqIntList "foldri"
                ([0, 1, 2], Vector.foldri (fn (i, _, acc) => i :: acc) [] v)
            end),

          Case ("find and findi", fn () =>
            let
              val v = Vector.fromList [1, 2, 3, 4]
            in
              A.eqIntOption "find" (SOME 2, Vector.find (fn x => x mod 2 = 0) v);
              A.eqIntOption "find misses" (NONE, Vector.find (fn x => x > 9) v);
              A.eqBy (op =, Show.option (Show.pair (Show.int, Show.int)))
                "findi returns the index too"
                (SOME (1, 2), Vector.findi (fn (_, x) => x mod 2 = 0) v)
            end),

          Case ("exists and all", fn () =>
            let
              val v = Vector.fromList [1, 2, 3]
              val empty = Vector.fromList ([] : int list)
            in
              A.eqBool "exists" (true, Vector.exists (fn x => x = 2) v);
              A.eqBool "exists misses" (false, Vector.exists (fn x => x = 9) v);
              A.eqBool "exists on empty" (false, Vector.exists (fn _ => true) empty);
              A.eqBool "all" (true, Vector.all (fn x => x > 0) v);
              A.eqBool "all misses" (false, Vector.all (fn x => x > 1) v);
              A.eqBool "all on empty" (true, Vector.all (fn _ => false) empty)
            end),

          Case ("collate", fn () =>
            (A.eqOrder "equal" (EQUAL,
               Vector.collate Int.compare
                 (Vector.fromList [1, 2], Vector.fromList [1, 2]));
             A.eqOrder "a prefix is less" (LESS,
               Vector.collate Int.compare
                 (Vector.fromList [1], Vector.fromList [1, 2]));
             A.eqOrder "first difference wins" (GREATER,
               Vector.collate Int.compare
                 (Vector.fromList [2], Vector.fromList [1, 9]))))
        ]),

        Group ("laws",
        [ P.forAll ("fromList and the fold are inverse", ints, Show.intList,
                    fn xs => toList (Vector.fromList xs) = xs),

          P.forAll ("length agrees with the list", ints, Show.intList,
                    fn xs => Vector.length (Vector.fromList xs) = List.length xs),

          P.forAll ("tabulate has the requested length", G.int (0, 30), Show.int,
                    fn n => Vector.length (Vector.tabulate (n, fn i => i)) = n),

          P.forAll ("tabulate agrees with List.tabulate", G.int (0, 30), Show.int,
                    fn n =>
                      toList (Vector.tabulate (n, fn i => i * 2))
                      = List.tabulate (n, fn i => i * 2)),

          P.forAll ("sub agrees with List.nth", vecAndIndex, showVecAndIndex,
                    fn (v, i) => Vector.sub (v, i) = List.nth (toList v, i)),

          P.forAll ("update changes exactly one position",
                    vecAndIndex, showVecAndIndex,
                    fn (v, i) =>
                      let
                        val v' = Vector.update (v, i, 999)
                      in
                        Vector.length v' = Vector.length v
                        andalso Vector.sub (v', i) = 999
                        andalso Vector.foldli
                                  (fn (j, x, acc) =>
                                     acc andalso (j = i orelse x = Vector.sub (v, j)))
                                  true v'
                      end),

          P.forAll ("map preserves length", vec, showV,
                    fn v => Vector.length (Vector.map (fn x => x + 1) v)
                            = Vector.length v),

          P.forAll ("map agrees with List.map", vec, showV,
                    fn v =>
                      toList (Vector.map (fn x => x * 3) v)
                      = List.map (fn x => x * 3) (toList v)),

          P.forAll ("mapi with the index ignored is map", vec, showV,
                    fn v =>
                      Vector.mapi (fn (_, x) => x * 3) v = Vector.map (fn x => x * 3) v),

          P.forAll ("foldr with cons rebuilds the list", vec, showV,
                    fn v => Vector.foldr op:: [] v = toList v),

          P.forAll ("foldl with cons reverses", vec, showV,
                    fn v => Vector.foldl op:: [] v = List.rev (toList v)),

          P.forAll ("foldli sees every index in order", vec, showV,
                    fn v =>
                      Vector.foldri (fn (i, _, acc) => i :: acc) [] v
                      = List.tabulate (Vector.length v, fn i => i)),

          P.forAll ("concat is additive over lengths",
                    G.list vec, Show.list showV,
                    fn vs =>
                      Vector.length (Vector.concat vs)
                      = List.foldl (fn (v, a) => a + Vector.length v) 0 vs),

          P.forAll ("concat agrees with list concatenation",
                    G.list vec, Show.list showV,
                    fn vs =>
                      toList (Vector.concat vs) = List.concat (List.map toList vs)),

          P.forAll ("find agrees with List.find", vec, showV,
                    fn v =>
                      Vector.find (fn x => x > 0) v
                      = List.find (fn x => x > 0) (toList v)),

          P.forAll ("exists is the dual of all", vec, showV,
                    fn v =>
                      Vector.exists (fn x => x > 0) v
                      = not (Vector.all (fn x => x <= 0) v)),

          P.forAll ("collate agrees with List.collate",
                    G.pair (vec, vec), Show.pair (showV, showV),
                    fn (a, b) =>
                      Vector.collate Int.compare (a, b)
                      = List.collate Int.compare (toList a, toList b))
        ])
      ])
  end
