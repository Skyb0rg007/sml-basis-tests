(* Tests for VectorSlice and ArraySlice.
 *
 * A slice is a window plus a reference to its underlying sequence, and the
 * tests below repeatedly check `base` so that an implementation which copies
 * instead of aliasing is caught.  For ArraySlice that aliasing is observable:
 * writing through a slice must be visible in the array it was cut from.
 *)

functor SliceTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure VS = VectorSlice
    structure AS = ArraySlice

    fun vlist v = Vector.foldr (op ::) [] v
    fun alist a = Array.foldr (op ::) [] a
    val ints = G.list G.smallInt
    val showL = Show.intList

    (* A list with a legal (start, length) window on it. *)
    val windowed =
      G.bind ints (fn xs =>
        G.bind (G.int (0, List.length xs)) (fn i =>
          G.map (fn n => (xs, i, n)) (G.int (0, List.length xs - i))))
    val showWindowed = Show.triple (showL, Show.int, Show.int)

    val suite = Group ("Slices",
      [ Group ("VectorSlice",
        [ Case ("full covers the vector", fn () =>
            let
              val v = Vector.fromList [1, 2, 3]
              val s = VS.full v
            in
              A.eqInt "length" (3, VS.length s);
              A.eqIntList "contents" ([1, 2, 3], vlist (VS.vector s));
              A.eqBy (op =, Show.triple (Show.vector Show.int, Show.int, Show.int))
                "base" ((v, 0, 3), VS.base s)
            end),

          Case ("slice cuts a window", fn () =>
            let
              val v = Vector.fromList [1, 2, 3, 4, 5]
            in
              A.eqIntList "with an explicit length"
                ([2, 3], vlist (VS.vector (VS.slice (v, 1, SOME 2))));
              A.eqIntList "to the end"
                ([2, 3, 4, 5], vlist (VS.vector (VS.slice (v, 1, NONE))));
              A.eqIntList "empty at the far end"
                ([], vlist (VS.vector (VS.slice (v, 5, NONE))));
              A.raises "start past the end" A.isSubscript
                (fn () => VS.slice (v, A.hide 6, NONE));
              A.raises "length past the end" A.isSubscript
                (fn () => VS.slice (v, A.hide 3, SOME 3));
              A.raises "negative start" A.isSubscript
                (fn () => VS.slice (v, A.hide ~1, NONE))
            end),

          Case ("subslice is relative to the slice", fn () =>
            let
              val v = Vector.fromList [1, 2, 3, 4, 5]
              val s = VS.slice (v, 1, SOME 3)          (* 2 3 4 *)
              val t = VS.subslice (s, 1, SOME 2)       (* 3 4 *)
            in
              A.eqIntList "contents" ([3, 4], vlist (VS.vector t));
              A.eqBy (op =, Show.triple (Show.vector Show.int, Show.int, Show.int))
                "base offsets are absolute" ((v, 2, 2), VS.base t);
              A.raises "outside the parent slice" A.isSubscript
                (fn () => VS.subslice (s, A.hide 1, SOME 3))
            end),

          Case ("sub, isEmpty and getItem", fn () =>
            let
              val s = VS.slice (Vector.fromList [1, 2, 3, 4], 1, SOME 2)
            in
              A.eqInt "sub is relative" (2, VS.sub (s, 0));
              A.raises "past the window" A.isSubscript (fn () => VS.sub (s, A.hide 2));
              A.eqBool "not empty" (false, VS.isEmpty s);
              A.eqBool "empty" (true,
                VS.isEmpty (VS.slice (Vector.fromList [1], 0, SOME 0)));
              case VS.getItem s of
                  NONE => A.fail "expected an item"
                | SOME (x, rest) =>
                    (A.eqInt "first item" (2, x);
                     A.eqIntList "rest" ([3], vlist (VS.vector rest)))
            end),

          Case ("traversal sees only the window", fn () =>
            let
              val s = VS.slice (Vector.fromList [1, 2, 3, 4, 5], 1, SOME 3)
            in
              A.eqInt "foldl" (9, VS.foldl op+ 0 s);
              A.eqIntList "foldr" ([2, 3, 4], VS.foldr op:: [] s);
              A.eqIntList "map" ([4, 6, 8], vlist (VS.map (fn x => x * 2) s));
              (* Indices restart at zero for the slice. *)
              A.eqIntList "foldli indices"
                ([2, 1, 0], VS.foldli (fn (i, _, acc) => i :: acc) [] s);
              A.eqIntOption "find" (SOME 4, VS.find (fn x => x > 3) s);
              A.eqBool "exists" (true, VS.exists (fn x => x = 3) s);
              A.eqBool "all" (false, VS.all (fn x => x > 2) s)
            end),

          Case ("concat", fn () =>
            A.eqIntList "joined"
              ([2, 3, 5],
               vlist (VS.concat [VS.slice (Vector.fromList [1, 2, 3], 1, SOME 2),
                                 VS.slice (Vector.fromList [4, 5], 1, SOME 1)]))),

          Case ("collate", fn () =>
            A.eqOrder "equal windows on different vectors" (EQUAL,
              VS.collate Int.compare
                (VS.slice (Vector.fromList [9, 1, 2], 1, SOME 2),
                 VS.full (Vector.fromList [1, 2]))))
        ]),

        Group ("ArraySlice",
        [ Case ("full and slice", fn () =>
            let
              val a = Array.fromList [1, 2, 3, 4, 5]
            in
              A.eqInt "full length" (5, AS.length (AS.full a));
              A.eqIntList "window"
                ([2, 3], vlist (AS.vector (AS.slice (a, 1, SOME 2))));
              A.eqBy (op =, Show.triple (Show.array Show.int, Show.int, Show.int))
                "base" ((a, 1, 2), AS.base (AS.slice (a, 1, SOME 2)));
              A.raises "past the end" A.isSubscript
                (fn () => AS.slice (a, A.hide 3, SOME 3))
            end),

          Case ("a slice writes through to its array", fn () =>
            let
              val a = Array.fromList [1, 2, 3, 4, 5]
              val s = AS.slice (a, 1, SOME 3)
            in
              AS.update (s, 0, 99);
              A.eqInt "seen through the slice" (99, AS.sub (s, 0));
              A.eqIntList "seen in the array" ([1, 99, 3, 4, 5], alist a);
              A.raises "update past the window" A.isSubscript
                (fn () => AS.update (s, A.hide 3, A.hide 0))
            end),

          Case ("modify affects only the window", fn () =>
            let
              val a = Array.fromList [1, 2, 3, 4, 5]
            in
              AS.modify (fn x => x * 10) (AS.slice (a, 1, SOME 3));
              A.eqIntList "outside the window is untouched"
                ([1, 20, 30, 40, 5], alist a)
            end),

          Case ("modifyi", fn () =>
            let
              val a = Array.fromList [0, 0, 0, 0]
            in
              AS.modifyi (fn (i, _) => i) (AS.slice (a, 1, SOME 2));
              A.eqIntList "indices restart at zero in the slice"
                ([0, 0, 1, 0], alist a)
            end),

          Case ("copy into an array", fn () =>
            let
              val src = Array.fromList [1, 2, 3, 4]
              val dst = Array.fromList [0, 0, 0, 0]
            in
              AS.copy {src = AS.slice (src, 1, SOME 2), dst = dst, di = 1};
              A.eqIntList "copied" ([0, 2, 3, 0], alist dst)
            end),

          (* Copying a slice onto an overlapping region of its own array is
           * specified to work as though the source were read first. *)
          Case ("overlapping copy shifts correctly", fn () =>
            let
              val a = Array.fromList [1, 2, 3, 4, 5]
            in
              AS.copy {src = AS.slice (a, 0, SOME 3), dst = a, di = 1};
              A.eqIntList "shifted right by one" ([1, 1, 2, 3, 5], alist a)
            end),

          Case ("overlapping copy shifting left", fn () =>
            let
              val a = Array.fromList [1, 2, 3, 4, 5]
            in
              AS.copy {src = AS.slice (a, 1, SOME 3), dst = a, di = 0};
              A.eqIntList "shifted left by one" ([2, 3, 4, 4, 5], alist a)
            end),

          Case ("copyVec", fn () =>
            let
              val dst = Array.fromList [0, 0, 0, 0]
            in
              AS.copyVec {src = VS.slice (Vector.fromList [1, 2, 3], 1, SOME 2),
                          dst = dst, di = 1};
              A.eqIntList "copied" ([0, 2, 3, 0], alist dst)
            end),

          Case ("getItem and traversal", fn () =>
            let
              val s = AS.slice (Array.fromList [1, 2, 3, 4, 5], 1, SOME 3)
            in
              A.eqInt "foldl" (9, AS.foldl op+ 0 s);
              A.eqIntList "foldr" ([2, 3, 4], AS.foldr op:: [] s);
              A.eqIntOption "find" (SOME 4, AS.find (fn x => x > 3) s);
              case AS.getItem s of
                  NONE => A.fail "expected an item"
                | SOME (x, rest) =>
                    (A.eqInt "head" (2, x);
                     A.eqInt "rest length" (2, AS.length rest))
            end)
        ]),

        Group ("laws",
        [ P.forAll ("a full slice denotes the whole vector", ints, showL,
                    fn xs =>
                      vlist (VS.vector (VS.full (Vector.fromList xs))) = xs),

          P.forAll ("a vector slice denotes the corresponding sublist",
                    windowed, showWindowed,
                    fn (xs, i, n) =>
                      vlist (VS.vector (VS.slice (Vector.fromList xs, i, SOME n)))
                      = List.take (List.drop (xs, i), n)),

          P.forAll ("slice length is the requested length",
                    windowed, showWindowed,
                    fn (xs, i, n) =>
                      VS.length (VS.slice (Vector.fromList xs, i, SOME n)) = n),

          P.forAll ("base recovers the slice arguments", windowed, showWindowed,
                    fn (xs, i, n) =>
                      let
                        val v = Vector.fromList xs
                        val (b, i', n') = VS.base (VS.slice (v, i, SOME n))
                      in
                        b = v andalso i' = i andalso n' = n
                      end),

          P.forAll ("a slice to the end runs to the end", windowed, showWindowed,
                    fn (xs, i, _) =>
                      vlist (VS.vector (VS.slice (Vector.fromList xs, i, NONE)))
                      = List.drop (xs, i)),

          P.forAll ("the three pieces around a window reassemble",
                    windowed, showWindowed,
                    fn (xs, i, n) =>
                      let
                        val v = Vector.fromList xs
                        fun part (a, b) = vlist (VS.vector (VS.slice (v, a, SOME b)))
                      in
                        part (0, i) @ part (i, n)
                        @ vlist (VS.vector (VS.slice (v, i + n, NONE)))
                        = xs
                      end),

          P.forAll ("array and vector slices agree", windowed, showWindowed,
                    fn (xs, i, n) =>
                      vlist (AS.vector (AS.slice (Array.fromList xs, i, SOME n)))
                      = vlist (VS.vector (VS.slice (Vector.fromList xs, i, SOME n)))),

          P.forAll ("folding a slice agrees with folding the sublist",
                    windowed, showWindowed,
                    fn (xs, i, n) =>
                      VS.foldr op:: [] (VS.slice (Vector.fromList xs, i, SOME n))
                      = List.take (List.drop (xs, i), n)),

          P.forAll ("modifying through a slice touches only the window",
                    windowed, showWindowed,
                    fn (xs, i, n) =>
                      let
                        val a = Array.fromList xs
                        val () = AS.modify (fn _ => 999) (AS.slice (a, i, SOME n))
                        val expected =
                          List.take (xs, i)
                          @ List.tabulate (n, fn _ => 999)
                          @ List.drop (xs, i + n)
                      in
                        alist a = expected
                      end),

          P.forAll ("subslice of the full slice is slice", windowed, showWindowed,
                    fn (xs, i, n) =>
                      let val v = Vector.fromList xs
                      in
                        vlist (VS.vector (VS.subslice (VS.full v, i, SOME n)))
                        = vlist (VS.vector (VS.slice (v, i, SOME n)))
                      end),

          P.forAll ("getItem peels one element at a time",
                    windowed, showWindowed,
                    fn (xs, i, n) =>
                      let
                        val s = VS.slice (Vector.fromList xs, i, SOME n)
                        fun drain s =
                          case VS.getItem s of
                              NONE => []
                            | SOME (x, rest) => x :: drain rest
                      in
                        drain s = List.take (List.drop (xs, i), n)
                      end),

          P.forAll ("concat of slices is concatenation of their contents",
                    G.list ints, Show.list showL,
                    fn xss =>
                      vlist (VS.concat
                               (List.map (VS.full o Vector.fromList) xss))
                      = List.concat xss)
        ])
      ])
  end
