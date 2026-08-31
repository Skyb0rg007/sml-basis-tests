(* Generic tests for MONO_VECTOR_SLICE and MONO_ARRAY_SLICE, instantiated for
 * each of the four required slice structures.  See gen-mono-seq.sml for why
 * these are written against the signature rather than four times over. *)

functor MonoVectorSliceTestsFn (structure Slice : MONO_VECTOR_SLICE
                                val name : string
                                val elem : int -> Slice.elem
                                val toInt : Slice.elem -> int
                                val ofInts : int list -> Slice.vector
                                val vectorToInts : Slice.vector -> int list) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    fun sInts s = vectorToInts (Slice.vector s)
    val showS = fn s => Show.intList (sInts s)
    fun cmp (a, b) = Int.compare (toInt a, toInt b)

    (* A list with a legal window on it. *)
    val windowed =
      G.bind (G.list (G.int (0, 255))) (fn ns =>
        G.bind (G.int (0, List.length ns)) (fn i =>
          G.map (fn n => (ns, i, n)) (G.int (0, List.length ns - i))))
    val showWindowed = Show.triple (Show.intList, Show.int, Show.int)

    val suite = Group (name,
      [ Case ("full, slice and subslice", fn () =>
          let
            val v = ofInts [1, 2, 3, 4, 5]
            val s = Slice.slice (v, 1, SOME 3)
          in
            A.eqIntList "full" ([1, 2, 3, 4, 5], sInts (Slice.full v));
            A.eqIntList "a window" ([2, 3, 4], sInts s);
            A.eqIntList "to the end" ([2, 3, 4, 5], sInts (Slice.slice (v, 1, NONE)));
            A.eqIntList "empty at the far end" ([], sInts (Slice.slice (v, 5, NONE)));
            A.eqIntList "subslice" ([3, 4], sInts (Slice.subslice (s, 1, SOME 2)));
            A.eqInt "length" (3, Slice.length s);
            A.raises "start past the end" A.isSubscript
              (fn () => Slice.slice (v, A.hide 6, NONE));
            A.raises "length past the end" A.isSubscript
              (fn () => Slice.slice (v, 3, SOME (A.hide 3)));
            A.raises "negative start" A.isSubscript
              (fn () => Slice.slice (v, A.hide ~1, NONE));
            A.raises "subslice outside the parent" A.isSubscript
              (fn () => Slice.subslice (s, 1, SOME (A.hide 3)))
          end),

        Case ("base reports the underlying sequence and window", fn () =>
          let
            val v = ofInts [1, 2, 3, 4, 5]
            val (b, i, n) = Slice.base (Slice.slice (v, 1, SOME 3))
          in
            A.eqIntList "the base sequence" ([1, 2, 3, 4, 5], vectorToInts b);
            A.eqInt "the offset" (1, i);
            A.eqInt "the length" (3, n)
          end),

        Case ("sub, isEmpty and getItem", fn () =>
          let val s = Slice.slice (ofInts [1, 2, 3, 4], 1, SOME 2)
          in
            A.eqInt "sub is relative to the window" (2, toInt (Slice.sub (s, 0)));
            A.raises "past the window" A.isSubscript
              (fn () => Slice.sub (s, A.hide 2));
            A.eqBool "not empty" (false, Slice.isEmpty s);
            A.eqBool "empty" (true, Slice.isEmpty (Slice.slice (ofInts [1], 0, SOME 0)));
            case Slice.getItem s of
                NONE => A.fail "expected an item"
              | SOME (x, rest) =>
                  (A.eqInt "head" (2, toInt x);
                   A.eqIntList "rest" ([3], sInts rest))
          end),

        Case ("traversal sees only the window", fn () =>
          let
            val s = Slice.slice (ofInts [1, 2, 3, 4, 5], 1, SOME 3)
            val seen = ref []
          in
            Slice.app (fn x => seen := toInt x :: !seen) s;
            A.eqIntList "app" ([4, 3, 2], !seen);
            seen := [];
            Slice.appi (fn (i, x) => seen := (i * 100 + toInt x) :: !seen) s;
            A.eqIntList "appi indices restart at zero" ([204, 103, 2], !seen);
            A.eqIntList "map"
              ([4, 6, 8], vectorToInts (Slice.map (fn x => elem (toInt x * 2)) s));
            A.eqIntList "mapi"
              ([0, 3, 8], vectorToInts (Slice.mapi (fn (i, x) => elem (i * toInt x)) s));
            A.eqIntList "foldl" ([4, 3, 2], Slice.foldl (fn (x, l) => toInt x :: l) [] s);
            A.eqIntList "foldr" ([2, 3, 4], Slice.foldr (fn (x, l) => toInt x :: l) [] s);
            A.eqIntList "foldli" ([2, 1, 0], Slice.foldli (fn (i, _, l) => i :: l) [] s);
            A.eqIntList "foldri" ([0, 1, 2], Slice.foldri (fn (i, _, l) => i :: l) [] s)
          end),

        Case ("searching and collate", fn () =>
          let val s = Slice.slice (ofInts [1, 2, 3, 4, 5], 1, SOME 3)
          in
            A.eqIntOption "find"
              (SOME 3, Option.map toInt (Slice.find (fn x => toInt x > 2) s));
            A.eqBy (op =, Show.option (Show.pair (Show.int, Show.int)))
              "findi" (SOME (1, 3),
                       Option.map (fn (i, x) => (i, toInt x))
                                  (Slice.findi (fn (_, x) => toInt x > 2) s));
            A.eqBool "exists" (true, Slice.exists (fn x => toInt x = 3) s);
            A.eqBool "all" (true, Slice.all (fn x => toInt x > 1) s);
            A.eqOrder "collate ignores the base"
              (EQUAL, Slice.collate cmp (s, Slice.full (ofInts [2, 3, 4])))
          end),

        Case ("concat", fn () =>
          A.eqIntList "joined"
            ([2, 3, 5],
             vectorToInts (Slice.concat [Slice.slice (ofInts [1, 2, 3], 1, SOME 2),
                                     Slice.slice (ofInts [4, 5], 1, SOME 1)]))),

        P.forAll ("a window denotes the corresponding sublist",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    sInts (Slice.slice (ofInts ns, i, SOME n))
                    = List.take (List.drop (ns, i), n)),

        P.forAll ("length is the requested length", windowed, showWindowed,
                  fn (ns, i, n) => Slice.length (Slice.slice (ofInts ns, i, SOME n)) = n),

        P.forAll ("base recovers the window", windowed, showWindowed,
                  fn (ns, i, n) =>
                    let val (_, i', n') = Slice.base (Slice.slice (ofInts ns, i, SOME n))
                    in i' = i andalso n' = n end),

        P.forAll ("slicing to the end runs to the end", windowed, showWindowed,
                  fn (ns, i, _) =>
                    sInts (Slice.slice (ofInts ns, i, NONE)) = List.drop (ns, i)),

        P.forAll ("the pieces around a window reassemble",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let val v = ofInts ns
                    in
                      sInts (Slice.slice (v, 0, SOME i))
                      @ sInts (Slice.slice (v, i, SOME n))
                      @ sInts (Slice.slice (v, i + n, NONE))
                      = ns
                    end),

        P.forAll ("subslice of the full slice is slice", windowed, showWindowed,
                  fn (ns, i, n) =>
                    let val v = ofInts ns
                    in
                      sInts (Slice.subslice (Slice.full v, i, SOME n))
                      = sInts (Slice.slice (v, i, SOME n))
                    end),

        P.forAll ("getItem peels one element at a time",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let
                      fun drain s =
                        case Slice.getItem s of
                            NONE => []
                          | SOME (x, rest) => toInt x :: drain rest
                    in
                      drain (Slice.slice (ofInts ns, i, SOME n))
                      = List.take (List.drop (ns, i), n)
                    end),

        P.forAll ("foldr rebuilds the window", windowed, showWindowed,
                  fn (ns, i, n) =>
                    Slice.foldr (fn (x, l) => toInt x :: l) []
                            (Slice.slice (ofInts ns, i, SOME n))
                    = List.take (List.drop (ns, i), n)),

        (* "length sl ... is equivalent to #3 (base sl)" and "full vec ... is
         * equivalent to slice(vec, 0, NONE)". *)
        P.forAll ("length is the third component of base, and full starts at zero",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let
                      val v = ofInts ns
                      val s = Slice.slice (v, i, SOME n)
                      val (_, _, k) = Slice.base s
                      val (_, fi, fn') = Slice.base (Slice.full v)
                      val (_, gi, gn) = Slice.base (Slice.slice (v, 0, NONE))
                    in
                      Slice.length s = k
                      andalso (fi, fn') = (gi, gn)
                    end),

        (* "the result is equivalent to
         *  Vector.tabulate (length sl, fn i => sub (sl, i))" *)
        P.forAll ("vector is the tabulation of the subscripts",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let val s = Slice.slice (ofInts ns, i, SOME n)
                    in
                      vectorToInts (Slice.vector s)
                      = List.tabulate (Slice.length s,
                                       fn k => toInt (Slice.sub (s, k)))
                    end),

        (* "The expression app f sl is equivalent to appi (f o #2) sl", and
         * the same shape for map, foldl and foldr. *)
        P.forAll ("the plain traversals are the indexed ones with the index dropped",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let
                      val s = Slice.slice (ofInts ns, i, SOME n)
                      val seen = ref []
                      val () = Slice.app (fn x => seen := toInt x :: !seen) s
                      val seenI = ref []
                      val () = Slice.appi ((fn x => seenI := toInt x :: !seenI) o #2) s
                      val f = fn (x, acc) => acc ^ Int.toString (toInt x)
                    in
                      !seen = !seenI
                      andalso vectorToInts (Slice.map (fn x => x) s)
                              = vectorToInts (Slice.mapi #2 s)
                      andalso Slice.foldl f "z" s
                              = Slice.foldli (fn (_, x, acc) => f (x, acc)) "z" s
                      andalso Slice.foldr f "z" s
                              = Slice.foldri (fn (_, x, acc) => f (x, acc)) "z" s
                    end),

        P.forAll ("the indexed traversals number the window from zero",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let val s = Slice.slice (ofInts ns, i, SOME n)
                    in
                      Slice.foldli (fn (k, _, acc) => k :: acc) [] s
                      = List.rev (List.tabulate (n, fn k => k))
                      andalso Slice.foldri (fn (k, _, acc) => k :: acc) [] s
                              = List.tabulate (n, fn k => k)
                    end),

        P.forAll ("isEmpty, find, exists, all and collate follow the contents",
                  G.pair (windowed, windowed),
                  Show.pair (showWindowed, showWindowed),
                  fn ((ns, i, n), (ms, j, m)) =>
                    let
                      val s = Slice.slice (ofInts ns, i, SOME n)
                      val t = Slice.slice (ofInts ms, j, SOME m)
                      val a = List.take (List.drop (ns, i), n)
                      val b = List.take (List.drop (ms, j), m)
                      val p = fn k => k > 100
                    in
                      Slice.isEmpty s = (Slice.length s = 0)
                      andalso Option.map toInt (Slice.find (fn x => p (toInt x)) s)
                              = List.find p a
                      andalso Slice.exists (fn x => p (toInt x)) s
                              = List.exists p a
                      andalso Slice.all (fn x => p (toInt x)) s = List.all p a
                      andalso Slice.collate cmp (s, t)
                              = List.collate Int.compare (a, b)
                    end),

        P.forAll ("concat is the concatenation of the windows",
                  G.list windowed, Show.list showWindowed,
                  fn ws =>
                    let
                      val slices =
                        List.map (fn (ns, i, n) => Slice.slice (ofInts ns, i, SOME n)) ws
                    in
                      vectorToInts (Slice.concat slices)
                      = List.concat
                          (List.map (fn (ns, i, n) =>
                                       List.take (List.drop (ns, i), n)) ws)
                    end),

        Case ("slice and subslice check every bound", fn () =>
          let
            val v = ofInts [1, 2, 3, 4, 5]
            val s = Slice.slice (v, 1, SOME 3)
          in
            A.raises "negative length" A.isSubscript
              (fn () => Slice.slice (v, 1, SOME (A.hide ~1)));
            A.raises "negative subslice start" A.isSubscript
              (fn () => Slice.subslice (s, A.hide ~1, NONE));
            A.raises "negative subslice length" A.isSubscript
              (fn () => Slice.subslice (s, 0, SOME (A.hide ~1)));
            A.raises "subslice start past the slice" A.isSubscript
              (fn () => Slice.subslice (s, A.hide 4, NONE));
            A.eqInt "an empty subslice at the very end is legal"
              (0, Slice.length (Slice.subslice (s, 3, NONE)));
            A.raises "sub at a negative index" A.isSubscript
              (fn () => Slice.sub (s, A.hide ~1));
            A.raises "sub past the window" A.isSubscript
              (fn () => Slice.sub (s, A.hide 3));
            A.that "getItem on an empty slice"
              (not (isSome (Slice.getItem (Slice.slice (v, 5, NONE)))))
          end)
      ])
  end

functor MonoArraySliceTestsFn (structure Slice : MONO_ARRAY_SLICE
                               val name : string
                               val elem : int -> Slice.elem
                               val toInt : Slice.elem -> int
                               val ofInts : int list -> Slice.array
                               val arrayToInts : Slice.array -> int list
                               val vectorToInts : Slice.vector -> int list
                               (* copyVec takes a slice of the corresponding
                                * vector type, not of the array type. *)
                               val vectorSliceOfInts : int list -> Slice.vector_slice) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    fun sInts s = vectorToInts (Slice.vector s)
    val showS = fn s => Show.intList (sInts s)
    fun cmp (a, b) = Int.compare (toInt a, toInt b)

    val windowed =
      G.bind (G.list (G.int (0, 255))) (fn ns =>
        G.bind (G.int (0, List.length ns)) (fn i =>
          G.map (fn n => (ns, i, n)) (G.int (0, List.length ns - i))))
    val showWindowed = Show.triple (Show.intList, Show.int, Show.int)

    val suite = Group (name,
      [ Case ("full, slice, subslice and base", fn () =>
          let
            val a = ofInts [1, 2, 3, 4, 5]
            val s = Slice.slice (a, 1, SOME 3)
            val (b, i, n) = Slice.base s
          in
            A.eqIntList "full" ([1, 2, 3, 4, 5], sInts (Slice.full a));
            A.eqIntList "a window" ([2, 3, 4], sInts s);
            A.eqIntList "to the end" ([2, 3, 4, 5], sInts (Slice.slice (a, 1, NONE)));
            A.eqIntList "subslice" ([3, 4], sInts (Slice.subslice (s, 1, SOME 2)));
            A.eqIntList "the base array" ([1, 2, 3, 4, 5], arrayToInts b);
            A.eqInt "the offset" (1, i);
            A.eqInt "the length" (3, n);
            A.eqInt "length" (3, Slice.length s);
            A.raises "past the end" A.isSubscript
              (fn () => Slice.slice (a, 3, SOME (A.hide 3)))
          end),

        Case ("a slice writes through to its array", fn () =>
          let
            val a = ofInts [1, 2, 3, 4, 5]
            val s = Slice.slice (a, 1, SOME 3)
          in
            Slice.update (s, 0, elem 99);
            A.eqInt "through the slice" (99, toInt (Slice.sub (s, 0)));
            A.eqIntList "in the array" ([1, 99, 3, 4, 5], arrayToInts a);
            A.raises "sub past the window" A.isSubscript
              (fn () => Slice.sub (s, A.hide 3));
            A.raises "update past the window" A.isSubscript
              (fn () => Slice.update (s, A.hide 3, elem 0))
          end),

        Case ("isEmpty and getItem", fn () =>
          let
            val a = ofInts [1, 2, 3]
            val s = Slice.slice (a, 1, SOME 2)
          in
            A.eqBool "not empty" (false, Slice.isEmpty s);
            A.eqBool "empty" (true, Slice.isEmpty (Slice.slice (a, 1, SOME 0)));
            case Slice.getItem s of
                NONE => A.fail "expected an item"
              | SOME (x, rest) =>
                  (A.eqInt "head" (2, toInt x);
                   A.eqInt "rest length" (1, Slice.length rest))
          end),

        Case ("copy and copyVec", fn () =>
          let
            val dst = ofInts [0, 0, 0, 0]
          in
            Slice.copy { src = Slice.slice (ofInts [1, 2, 3], 1, SOME 2),
                     dst = dst, di = 1 };
            A.eqIntList "copy" ([0, 2, 3, 0], arrayToInts dst);
            Slice.copyVec { src = vectorSliceOfInts [7], dst = dst, di = 3 };
            A.eqIntList "copyVec" ([0, 2, 3, 7], arrayToInts dst);
            A.raises "copyVec past the end" A.isSubscript
              (fn () => Slice.copyVec { src = vectorSliceOfInts [1, 2],
                                    dst = dst, di = A.hide 3 })
          end),

        Case ("overlapping copy within one array", fn () =>
          let val a = ofInts [1, 2, 3, 4, 5]
          in
            Slice.copy { src = Slice.slice (a, 0, SOME 3), dst = a, di = 1 };
            A.eqIntList "shifted right by one" ([1, 1, 2, 3, 5], arrayToInts a)
          end),

        Case ("traversal, modify and modifyi", fn () =>
          let
            val a = ofInts [1, 2, 3, 4, 5]
            val s = Slice.slice (a, 1, SOME 3)
            val seen = ref []
          in
            Slice.app (fn x => seen := toInt x :: !seen) s;
            A.eqIntList "app" ([4, 3, 2], !seen);
            seen := [];
            Slice.appi (fn (i, x) => seen := (i * 100 + toInt x) :: !seen) s;
            A.eqIntList "appi" ([204, 103, 2], !seen);
            A.eqIntList "foldl" ([4, 3, 2], Slice.foldl (fn (x, l) => toInt x :: l) [] s);
            A.eqIntList "foldr" ([2, 3, 4], Slice.foldr (fn (x, l) => toInt x :: l) [] s);
            A.eqIntList "foldli" ([2, 1, 0], Slice.foldli (fn (i, _, l) => i :: l) [] s);
            A.eqIntList "foldri" ([0, 1, 2], Slice.foldri (fn (i, _, l) => i :: l) [] s);
            Slice.modify (fn x => elem (toInt x * 10)) s;
            A.eqIntList "modify touches only the window"
              ([1, 20, 30, 40, 5], arrayToInts a);
            Slice.modifyi (fn (i, _) => elem i) s;
            A.eqIntList "modifyi indices restart at zero"
              ([1, 0, 1, 2, 5], arrayToInts a)
          end),

        Case ("searching and collate", fn () =>
          let val s = Slice.slice (ofInts [1, 2, 3, 4, 5], 1, SOME 3)
          in
            A.eqIntOption "find"
              (SOME 3, Option.map toInt (Slice.find (fn x => toInt x > 2) s));
            A.eqBy (op =, Show.option (Show.pair (Show.int, Show.int)))
              "findi" (SOME (1, 3),
                       Option.map (fn (i, x) => (i, toInt x))
                                  (Slice.findi (fn (_, x) => toInt x > 2) s));
            A.eqBool "exists" (true, Slice.exists (fn x => toInt x = 3) s);
            A.eqBool "all" (true, Slice.all (fn x => toInt x > 1) s);
            A.eqOrder "collate"
              (EQUAL, Slice.collate cmp (s, Slice.full (ofInts [2, 3, 4])))
          end),

        Case ("vector takes a snapshot of the window", fn () =>
          let
            val a = ofInts [1, 2, 3]
            val s = Slice.slice (a, 0, SOME 2)
            val snapshot = Slice.vector s
          in
            Slice.update (s, 0, elem 99);
            A.eqIntList "the snapshot does not follow the array"
              ([1, 2], vectorToInts snapshot)
          end),

        P.forAll ("a window denotes the corresponding sublist",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    sInts (Slice.slice (ofInts ns, i, SOME n))
                    = List.take (List.drop (ns, i), n)),

        P.forAll ("modifying through a slice touches only the window",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let
                      val a = ofInts ns
                      val () = Slice.modify (fn _ => elem 99) (Slice.slice (a, i, SOME n))
                    in
                      arrayToInts a
                      = List.take (ns, i) @ List.tabulate (n, fn _ => 99)
                        @ List.drop (ns, i + n)
                    end),

        P.forAll ("copying a slice into a fresh array preserves it",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let
                      val dst = ofInts (List.tabulate (n, fn _ => 0))
                    in
                      Slice.copy { src = Slice.slice (ofInts ns, i, SOME n),
                               dst = dst, di = 0 };
                      arrayToInts dst = List.take (List.drop (ns, i), n)
                    end),

        P.forAll ("copyVec writes a vector into an array",
                  G.list (G.int (0, 255)), Show.intList,
                  fn ns =>
                    let
                      val dst = ofInts (List.map (fn _ => 0) ns)
                    in
                      Slice.copyVec { src = vectorSliceOfInts ns, dst = dst, di = 0 };
                      arrayToInts dst = ns
                    end),

        P.forAll ("getItem peels one element at a time",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let
                      fun drain s =
                        case Slice.getItem s of
                            NONE => []
                          | SOME (x, rest) => toInt x :: drain rest
                    in
                      drain (Slice.slice (ofInts ns, i, SOME n))
                      = List.take (List.drop (ns, i), n)
                    end),

        P.forAll ("length is the third component of base, and full starts at zero",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let
                      val a = ofInts ns
                      val s = Slice.slice (a, i, SOME n)
                      val (_, _, k) = Slice.base s
                      val (_, fi, fn') = Slice.base (Slice.full a)
                      val (_, gi, gn) = Slice.base (Slice.slice (a, 0, NONE))
                    in
                      Slice.length s = k andalso (fi, fn') = (gi, gn)
                    end),

        P.forAll ("vector is the tabulation of the subscripts",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let val s = Slice.slice (ofInts ns, i, SOME n)
                    in
                      vectorToInts (Slice.vector s)
                      = List.tabulate (Slice.length s,
                                       fn k => toInt (Slice.sub (s, k)))
                    end),

        (* "The expression modify f sl is equivalent to modifyi (f o #2) sl",
         * and the same shape for app, foldl and foldr. *)
        P.forAll ("the plain traversals are the indexed ones with the index dropped",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let
                      val f = fn x => elem ((toInt x * 3 + 1) mod 128)
                      val a = ofInts ns
                      val b = ofInts ns
                      val () = Slice.modify f (Slice.slice (a, i, SOME n))
                      val () = Slice.modifyi (f o #2) (Slice.slice (b, i, SOME n))
                      val c = Slice.slice (ofInts ns, i, SOME n)
                      val g = fn (x, acc) => acc ^ Int.toString (toInt x)
                      val seen = ref []
                      val () = Slice.app (fn x => seen := toInt x :: !seen) c
                      val seenI = ref []
                      val () = Slice.appi ((fn x => seenI := toInt x :: !seenI) o #2) c
                    in
                      arrayToInts a = arrayToInts b
                      andalso !seen = !seenI
                      andalso Slice.foldl g "z" c
                              = Slice.foldli (fn (_, x, acc) => g (x, acc)) "z" c
                      andalso Slice.foldr g "z" c
                              = Slice.foldri (fn (_, x, acc) => g (x, acc)) "z" c
                    end),

        P.forAll ("the indexed traversals number the window from zero",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let
                      val a = ofInts ns
                      val s = Slice.slice (a, i, SOME n)
                      val seen = ref []
                      val () = Slice.appi (fn (k, _) => seen := k :: !seen) s
                      val touched = ref []
                      val () = Slice.modifyi (fn (k, x) =>
                                                (touched := k :: !touched; x)) s
                    in
                      List.rev (!seen) = List.tabulate (n, fn k => k)
                      andalso List.rev (!touched) = List.tabulate (n, fn k => k)
                      andalso arrayToInts a = ns
                      andalso Slice.foldli (fn (k, _, acc) => k :: acc) [] s
                              = List.rev (List.tabulate (n, fn k => k))
                      andalso Slice.foldri (fn (k, _, acc) => k :: acc) [] s
                              = List.tabulate (n, fn k => k)
                    end),

        P.forAll ("isEmpty, find, exists, all and collate follow the contents",
                  G.pair (windowed, windowed),
                  Show.pair (showWindowed, showWindowed),
                  fn ((ns, i, n), (ms, j, m)) =>
                    let
                      val s = Slice.slice (ofInts ns, i, SOME n)
                      val t = Slice.slice (ofInts ms, j, SOME m)
                      val a = List.take (List.drop (ns, i), n)
                      val b = List.take (List.drop (ms, j), m)
                      val p = fn k => k > 100
                    in
                      Slice.isEmpty s = (Slice.length s = 0)
                      andalso Option.map toInt (Slice.find (fn x => p (toInt x)) s)
                              = List.find p a
                      andalso Slice.exists (fn x => p (toInt x)) s
                              = List.exists p a
                      andalso Slice.all (fn x => p (toInt x)) s = List.all p a
                      andalso Slice.collate cmp (s, t)
                              = List.collate Int.compare (a, b)
                    end),

        (* "the i(th) element of src ... being copied to position di + i in
         * the destination array.  If di < 0 or if |dst| < di+|src|, then the
         * Subscript exception is raised." *)
        P.forAll ("copy and copyVec place the window at the offset",
                  windowed, showWindowed,
                  fn (ns, i, n) =>
                    let
                      val window = List.take (List.drop (ns, i), n)
                      val dst = ofInts (List.tabulate (n + 2, fn _ => 0))
                      val dst2 = ofInts (List.tabulate (n + 2, fn _ => 0))
                    in
                      Slice.copy { src = Slice.slice (ofInts ns, i, SOME n),
                                   dst = dst, di = 2 };
                      Slice.copyVec { src = vectorSliceOfInts window,
                                      dst = dst2, di = 2 };
                      arrayToInts dst = [0, 0] @ window
                      andalso arrayToInts dst2 = [0, 0] @ window
                    end),

        Case ("slice, subslice and copy check every bound", fn () =>
          let
            val a = ofInts [1, 2, 3, 4, 5]
            val s = Slice.slice (a, 1, SOME 3)
            val dst = ofInts [0, 0]
          in
            A.raises "negative start" A.isSubscript
              (fn () => Slice.slice (a, A.hide ~1, NONE));
            A.raises "negative length" A.isSubscript
              (fn () => Slice.slice (a, 1, SOME (A.hide ~1)));
            A.raises "negative subslice start" A.isSubscript
              (fn () => Slice.subslice (s, A.hide ~1, NONE));
            A.raises "sub at a negative index" A.isSubscript
              (fn () => Slice.sub (s, A.hide ~1));
            A.raises "update at a negative index" A.isSubscript
              (fn () => Slice.update (s, A.hide ~1, elem 0));
            A.raises "copy with a negative offset" A.isSubscript
              (fn () => Slice.copy { src = s, dst = dst, di = A.hide ~1 });
            A.raises "copy into a destination that is too small" A.isSubscript
              (fn () => Slice.copy { src = s, dst = dst, di = A.hide 0 });
            A.raises "copyVec with a negative offset" A.isSubscript
              (fn () => Slice.copyVec { src = vectorSliceOfInts [1],
                                        dst = dst, di = A.hide ~1 });
            A.raises "copyVec into a destination that is too small" A.isSubscript
              (fn () => Slice.copyVec { src = vectorSliceOfInts [1, 2, 3],
                                        dst = dst, di = A.hide 0 });
            A.that "getItem on an empty slice"
              (not (isSome (Slice.getItem (Slice.slice (a, 5, NONE)))))
          end)
      ])
  end
