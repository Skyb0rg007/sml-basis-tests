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

          Case ("app, appi, mapi and findi see only the window", fn () =>
            let
              val s = VS.slice (Vector.fromList [1, 2, 3, 4, 5], 1, SOME 3)
              val seen = ref []
            in
              VS.app (fn x => seen := x :: !seen) s;
              A.eqIntList "app" ([4, 3, 2], !seen);
              seen := [];
              VS.appi (fn (i, x) => seen := (i * 100 + x) :: !seen) s;
              A.eqIntList "appi indices restart at zero" ([204, 103, 2], !seen);
              A.eqIntList "mapi" ([0, 3, 8],
                vlist (VS.mapi (fn (i, x) => i * x) s));
              A.eqBy (op =, Show.option (Show.pair (Show.int, Show.int)))
                "findi returns the index within the slice"
                (SOME (1, 3), VS.findi (fn (_, x) => x > 2) s)
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
                 VS.full (Vector.fromList [1, 2])))),

          Case ("slice and subslice check every bound", fn () =>
            let
              val v = Vector.fromList [1, 2, 3, 4, 5]
              val s = VS.slice (v, 1, SOME 3)
            in
              A.raises "negative length" A.isSubscript
                (fn () => VS.slice (v, A.hide 1, SOME (A.hide ~1)));
              A.raises "start past the end with a length" A.isSubscript
                (fn () => VS.slice (v, A.hide 6, SOME (A.hide 0)));
              A.eqInt "an empty slice at the very end is legal"
                (0, VS.length (VS.slice (v, 5, SOME 0)));
              A.raises "negative subslice start" A.isSubscript
                (fn () => VS.subslice (s, A.hide ~1, NONE));
              A.raises "negative subslice length" A.isSubscript
                (fn () => VS.subslice (s, A.hide 0, SOME (A.hide ~1)));
              A.raises "subslice start past the slice" A.isSubscript
                (fn () => VS.subslice (s, A.hide 4, NONE));
              A.eqInt "an empty subslice at the very end is legal"
                (0, VS.length (VS.subslice (s, 3, NONE)));
              A.raises "sub on a negative index" A.isSubscript
                (fn () => VS.sub (s, A.hide ~1))
            end),

          Case ("getItem on an empty slice", fn () =>
            A.that "no item"
              (not (isSome (VS.getItem (VS.slice (Vector.fromList [1, 2], 1, SOME 0))))))
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

          Case ("subslice narrows an array slice", fn () =>
            let
              val a = Array.fromList [1, 2, 3, 4, 5]
              val s = AS.slice (a, 1, SOME 3)          (* 2 3 4 *)
              val t = AS.subslice (s, 1, SOME 2)       (* 3 4 *)
            in
              A.eqIntList "contents" ([3, 4], vlist (AS.vector t));
              A.eqBy (op =, Show.triple (Show.array Show.int, Show.int, Show.int))
                "base offsets are absolute" ((a, 2, 2), AS.base t);
              A.raises "outside the parent slice" A.isSubscript
                (fn () => AS.subslice (s, 1, SOME (A.hide 3)))
            end),

          Case ("appi, mapi and findi on an array slice", fn () =>
            let
              val s = AS.slice (Array.fromList [1, 2, 3, 4, 5], 1, SOME 3)
              val seen = ref []
            in
              AS.appi (fn (i, x) => seen := (i * 100 + x) :: !seen) s;
              A.eqIntList "appi indices restart at zero" ([204, 103, 2], !seen);
              A.eqBy (op =, Show.option (Show.pair (Show.int, Show.int)))
                "findi" (SOME (1, 3), AS.findi (fn (_, x) => x > 2) s)
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
            end),

          Case ("exists, all, isEmpty and collate on an array slice", fn () =>
            let
              val s = AS.slice (Array.fromList [1, 2, 3, 4, 5], 1, SOME 3)
            in
              A.eqBool "exists" (true, AS.exists (fn x => x = 3) s);
              A.eqBool "exists misses" (false, AS.exists (fn x => x = 5) s);
              A.eqBool "all" (true, AS.all (fn x => x > 1) s);
              A.eqBool "all misses" (false, AS.all (fn x => x > 2) s);
              A.eqBool "not empty" (false, AS.isEmpty s);
              A.eqBool "an empty window"
                (true, AS.isEmpty (AS.slice (Array.fromList [1], 0, SOME 0)));
              A.that "no item in an empty slice"
                (not (isSome (AS.getItem
                                (AS.slice (Array.fromList [1], 1, NONE)))));
              A.eqOrder "collate of equal windows on different arrays" (EQUAL,
                AS.collate Int.compare
                  (s, AS.full (Array.fromList [2, 3, 4])));
              A.eqOrder "a prefix is less" (LESS,
                AS.collate Int.compare
                  (AS.full (Array.fromList [2, 3]), s))
            end),

          Case ("slice, subslice and copy check every bound", fn () =>
            let
              val a = Array.fromList [1, 2, 3, 4, 5]
              val s = AS.slice (a, 1, SOME 3)
              val dst = Array.fromList [0, 0]
            in
              A.raises "negative start" A.isSubscript
                (fn () => AS.slice (a, A.hide ~1, NONE));
              A.raises "negative length" A.isSubscript
                (fn () => AS.slice (a, A.hide 1, SOME (A.hide ~1)));
              A.raises "start past the end" A.isSubscript
                (fn () => AS.slice (a, A.hide 6, NONE));
              A.eqInt "an empty slice at the very end is legal"
                (0, AS.length (AS.slice (a, 5, NONE)));
              A.raises "negative subslice start" A.isSubscript
                (fn () => AS.subslice (s, A.hide ~1, NONE));
              A.raises "sub on a negative index" A.isSubscript
                (fn () => AS.sub (s, A.hide ~1));
              A.raises "copy with a negative offset" A.isSubscript
                (fn () => AS.copy {src = s, dst = dst, di = A.hide ~1});
              A.raises "copy into a destination that is too small" A.isSubscript
                (fn () => AS.copy {src = s, dst = dst, di = A.hide 0});
              A.raises "copyVec with a negative offset" A.isSubscript
                (fn () => AS.copyVec {src = VS.full (Vector.fromList [1, 2]),
                                      dst = dst, di = A.hide ~1});
              A.raises "copyVec into a destination that is too small"
                A.isSubscript
                (fn () => AS.copyVec {src = VS.full (Vector.fromList [1, 2, 3]),
                                      dst = dst, di = A.hide 0})
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

          (* "length sl ... is equivalent to #3 (base sl)", and
           * "full arr ... is equivalent to slice(arr, 0, NONE)". *)
          P.forAll ("length is the third component of base", windowed, showWindowed,
                    fn (xs, i, n) =>
                      let
                        val v = Vector.fromList xs
                        val s = VS.slice (v, i, SOME n)
                        val (_, _, k) = VS.base s
                      in
                        VS.length s = k andalso k = n
                      end),

          P.forAll ("full is the slice from zero to the end", ints, showL,
                    fn xs =>
                      let
                        val v = Vector.fromList xs
                        val a = Array.fromList xs
                      in
                        VS.base (VS.full v) = VS.base (VS.slice (v, 0, NONE))
                        andalso AS.base (AS.full a)
                                = AS.base (AS.slice (a, 0, NONE))
                      end),

          (* "the result is equivalent to
           *  Vector.tabulate (length sl, fn i => sub (sl, i))" *)
          P.forAll ("vector is the tabulation of the subscripts",
                    windowed, showWindowed,
                    fn (xs, i, n) =>
                      let
                        val s = VS.slice (Vector.fromList xs, i, SOME n)
                        val t = AS.slice (Array.fromList xs, i, SOME n)
                      in
                        VS.vector s
                        = Vector.tabulate (VS.length s, fn k => VS.sub (s, k))
                        andalso AS.vector t
                                = Vector.tabulate (AS.length t,
                                                   fn k => AS.sub (t, k))
                      end),

          (* "The expression app f sl is equivalent to appi (f o #2) sl", and
           * likewise modify, foldl and foldr. *)
          P.forAll ("the plain traversals are the indexed ones with the index dropped",
                    windowed, showWindowed,
                    fn (xs, i, n) =>
                      let
                        val s = VS.slice (Vector.fromList xs, i, SOME n)
                        val f = fn (a, acc) => acc ^ Int.toString a
                        val seen = ref []
                        val () = VS.app (fn x => seen := x :: !seen) s
                        val seenI = ref []
                        val () = VS.appi ((fn x => seenI := x :: !seenI) o #2) s
                      in
                        !seen = !seenI
                        andalso VS.foldl f "z" s
                                = VS.foldli (fn (_, a, acc) => f (a, acc)) "z" s
                        andalso VS.foldr f "z" s
                                = VS.foldri (fn (_, a, acc) => f (a, acc)) "z" s
                        andalso VS.map (fn x => x + 1) s
                                = VS.mapi ((fn x => x + 1) o #2) s
                      end),

          P.forAll ("modify is modifyi with the index dropped",
                    windowed, showWindowed,
                    fn (xs, i, n) =>
                      let
                        val f = fn x => x * 3 + 1
                        val a = Array.fromList xs
                        val b = Array.fromList xs
                      in
                        AS.modify f (AS.slice (a, i, SOME n));
                        AS.modifyi (f o #2) (AS.slice (b, i, SOME n));
                        alist a = alist b
                      end),

          P.forAll ("the array slice folds agree with the indexed ones",
                    windowed, showWindowed,
                    fn (xs, i, n) =>
                      let
                        val t = AS.slice (Array.fromList xs, i, SOME n)
                        val f = fn (a, acc) => acc ^ Int.toString a
                      in
                        AS.foldl f "z" t
                        = AS.foldli (fn (_, a, acc) => f (a, acc)) "z" t
                        andalso AS.foldr f "z" t
                                = AS.foldri (fn (_, a, acc) => f (a, acc)) "z" t
                        andalso AS.foldli (fn (k, _, acc) => k :: acc) [] t
                                = List.rev (List.tabulate (n, fn k => k))
                      end),

          P.forAll ("isEmpty is a test on the length", windowed, showWindowed,
                    fn (xs, i, n) =>
                      let
                        val s = VS.slice (Vector.fromList xs, i, SOME n)
                        val t = AS.slice (Array.fromList xs, i, SOME n)
                      in
                        VS.isEmpty s = (VS.length s = 0)
                        andalso AS.isEmpty t = (AS.length t = 0)
                      end),

          P.forAll ("find, exists and all agree with the list versions",
                    windowed, showWindowed,
                    fn (xs, i, n) =>
                      let
                        val window = List.take (List.drop (xs, i), n)
                        val s = VS.slice (Vector.fromList xs, i, SOME n)
                        val t = AS.slice (Array.fromList xs, i, SOME n)
                        val p = fn x => x > 0
                      in
                        VS.find p s = List.find p window
                        andalso VS.exists p s = List.exists p window
                        andalso VS.all p s = List.all p window
                        andalso AS.find p t = List.find p window
                        andalso AS.exists p t = List.exists p window
                        andalso AS.all p t = List.all p window
                      end),

          P.forAll ("collate on slices agrees with List.collate",
                    G.pair (windowed, windowed),
                    Show.pair (showWindowed, showWindowed),
                    fn ((xs, i, n), (ys, j, m)) =>
                      let
                        val a = List.take (List.drop (xs, i), n)
                        val b = List.take (List.drop (ys, j), m)
                      in
                        VS.collate Int.compare
                          (VS.slice (Vector.fromList xs, i, SOME n),
                           VS.slice (Vector.fromList ys, j, SOME m))
                        = List.collate Int.compare (a, b)
                        andalso AS.collate Int.compare
                                  (AS.slice (Array.fromList xs, i, SOME n),
                                   AS.slice (Array.fromList ys, j, SOME m))
                                = List.collate Int.compare (a, b)
                      end),

          (* "the i(th) element of src ... being copied to position di + i in
           * the destination array" *)
          P.forAll ("copy and copyVec place the window at the offset",
                    windowed, showWindowed,
                    fn (xs, i, n) =>
                      let
                        val window = List.take (List.drop (xs, i), n)
                        val dst = Array.array (n + 2, 0)
                        val dst2 = Array.array (n + 2, 0)
                      in
                        AS.copy {src = AS.slice (Array.fromList xs, i, SOME n),
                                 dst = dst, di = 2};
                        AS.copyVec {src = VS.slice (Vector.fromList xs, i, SOME n),
                                    dst = dst2, di = 2};
                        alist dst = [0, 0] @ window
                        andalso alist dst2 = [0, 0] @ window
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
