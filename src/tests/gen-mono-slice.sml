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
                    = List.take (List.drop (ns, i), n))
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
                    end)
      ])
  end
