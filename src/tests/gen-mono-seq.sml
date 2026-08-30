(* Generic tests for the monomorphic sequence signatures.
 *
 * The Basis requires four monomorphic sequence structures over char and four
 * over Word8, each a separate implementation of MONO_VECTOR, MONO_ARRAY,
 * MONO_VECTOR_SLICE or MONO_ARRAY_SLICE.  Testing all eight by hand would be
 * eight copies of the same file, so the tests are written once against the
 * signature and instantiated for each.
 *
 * The element type is abstract in these signatures -- it is not even an
 * equality type -- so each instantiation supplies conversions to and from int,
 * and everything is compared through those.
 *)

functor MonoVectorTestsFn (structure Seq : MONO_VECTOR
                           val name : string
                           val elem : int -> Seq.elem
                           val toInt : Seq.elem -> int) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    fun ints v = List.map toInt (Seq.foldr (op ::) [] v)
    fun ofInts ns = Seq.fromList (List.map elem ns)
    fun eqV msg (e, a) = A.eqIntList msg (ints e, ints a)
    val showV = fn v => Show.intList (ints v)
    fun cmp (a, b) = Int.compare (toInt a, toInt b)

    val genInts = G.list (G.int (0, 255))
    val genV = G.map ofInts genInts

    val withIndex =
      G.bind (G.filter (fn v => Seq.length v > 0) genV) (fn v =>
        G.map (fn i => (v, i)) (G.int (0, Seq.length v - 1)))
    val showWithIndex = Show.pair (showV, Show.int)

    val suite = Group (name,
      [ Case ("construction", fn () =>
          (A.that "maxLen is non-negative" (Seq.maxLen >= 0);
           A.eqIntList "fromList" ([1, 2, 3], ints (ofInts [1, 2, 3]));
           A.eqInt "length" (3, Seq.length (ofInts [1, 2, 3]));
           A.eqInt "the empty sequence" (0, Seq.length (ofInts []));
           A.eqIntList "tabulate"
             ([0, 2, 4], ints (Seq.tabulate (3, fn i => elem (i * 2))));
           A.raises "negative tabulate" A.isSize
             (fn () => Seq.tabulate (A.hide ~1, fn _ => elem 0)))),

        Case ("sub and update", fn () =>
          let val v = ofInts [1, 2, 3]
          in
            A.eqInt "first" (1, toInt (Seq.sub (v, 0)));
            A.eqInt "last" (3, toInt (Seq.sub (v, 2)));
            A.raises "past the end" A.isSubscript
              (fn () => Seq.sub (v, A.hide 3));
            A.raises "negative" A.isSubscript (fn () => Seq.sub (v, A.hide ~1));
            A.eqIntList "update returns a new sequence"
              ([1, 9, 3], ints (Seq.update (v, 1, elem 9)));
            A.eqIntList "and leaves the original alone" ([1, 2, 3], ints v);
            A.raises "update past the end" A.isSubscript
              (fn () => Seq.update (v, A.hide 3, elem 0));
            A.raises "update negative" A.isSubscript
              (fn () => Seq.update (v, A.hide ~1, elem 0))
          end),

        Case ("concat", fn () =>
          (A.eqIntList "several"
             ([1, 2, 3], ints (Seq.concat [ofInts [1], ofInts [], ofInts [2, 3]]));
           A.eqInt "nothing" (0, Seq.length (Seq.concat [])))),

        Case ("app and appi visit in order", fn () =>
          let
            val v = ofInts [10, 20, 30]
            val seen = ref []
          in
            Seq.app (fn x => seen := toInt x :: !seen) v;
            A.eqIntList "app" ([30, 20, 10], !seen);
            seen := [];
            Seq.appi (fn (i, x) => seen := (i * 100 + toInt x) :: !seen) v;
            A.eqIntList "appi sees the index" ([230, 120, 10], !seen)
          end),

        Case ("map and mapi", fn () =>
          (A.eqIntList "map"
             ([2, 4, 6], ints (Seq.map (fn x => elem (toInt x * 2)) (ofInts [1, 2, 3])));
           A.eqIntList "mapi"
             ([0, 2, 6], ints (Seq.mapi (fn (i, x) => elem (i * toInt x))
                                      (ofInts [1, 2, 3]))))),

        Case ("the folds", fn () =>
          let val v = ofInts [1, 2, 3]
          in
            A.eqInt "foldl" (6, Seq.foldl (fn (x, a) => a + toInt x) 0 v);
            A.eqInt "foldr" (6, Seq.foldr (fn (x, a) => a + toInt x) 0 v);
            A.eqIntList "foldl visits left to right"
              ([3, 2, 1], Seq.foldl (fn (x, a) => toInt x :: a) [] v);
            A.eqIntList "foldr visits right to left"
              ([1, 2, 3], Seq.foldr (fn (x, a) => toInt x :: a) [] v);
            A.eqIntList "foldli indices"
              ([2, 1, 0], Seq.foldli (fn (i, _, a) => i :: a) [] v);
            A.eqIntList "foldri indices"
              ([0, 1, 2], Seq.foldri (fn (i, _, a) => i :: a) [] v)
          end),

        Case ("searching", fn () =>
          let val v = ofInts [1, 2, 3, 4]
          in
            A.eqIntOption "find"
              (SOME 2, Option.map toInt (Seq.find (fn x => toInt x mod 2 = 0) v));
            A.eqIntOption "find misses"
              (NONE, Option.map toInt (Seq.find (fn x => toInt x > 9) v));
            A.eqBy (op =, Show.option (Show.pair (Show.int, Show.int)))
              "findi returns the index too"
              (SOME (1, 2),
               Option.map (fn (i, x) => (i, toInt x))
                          (Seq.findi (fn (_, x) => toInt x mod 2 = 0) v));
            A.eqBool "exists" (true, Seq.exists (fn x => toInt x = 3) v);
            A.eqBool "exists misses" (false, Seq.exists (fn x => toInt x = 9) v);
            A.eqBool "exists on the empty sequence"
              (false, Seq.exists (fn _ => true) (ofInts []));
            A.eqBool "all" (true, Seq.all (fn x => toInt x > 0) v);
            A.eqBool "all misses" (false, Seq.all (fn x => toInt x > 1) v);
            A.eqBool "all on the empty sequence"
              (true, Seq.all (fn _ => false) (ofInts []))
          end),

        Case ("collate", fn () =>
          (A.eqOrder "equal" (EQUAL, Seq.collate cmp (ofInts [1, 2], ofInts [1, 2]));
           A.eqOrder "a prefix is less"
             (LESS, Seq.collate cmp (ofInts [1], ofInts [1, 2]));
           A.eqOrder "the first difference wins"
             (GREATER, Seq.collate cmp (ofInts [2], ofInts [1, 9])))),

        P.forAll ("fromList and the fold are inverse", genInts, Show.intList,
                  fn ns => ints (ofInts ns) = ns),

        P.forAll ("length agrees with the list", genInts, Show.intList,
                  fn ns => Seq.length (ofInts ns) = List.length ns),

        P.forAll ("sub agrees with the list", withIndex, showWithIndex,
                  fn (v, i) => toInt (Seq.sub (v, i)) = List.nth (ints v, i)),

        P.forAll ("update changes exactly one position",
                  withIndex, showWithIndex,
                  fn (v, i) =>
                    let val v' = Seq.update (v, i, elem 99)
                    in
                      Seq.length v' = Seq.length v
                      andalso toInt (Seq.sub (v', i)) = 99
                      andalso Seq.foldli
                                (fn (j, x, acc) =>
                                   acc andalso (j = i
                                                orelse toInt x = toInt (Seq.sub (v, j))))
                                true v'
                    end),

        P.forAll ("map preserves length", genV, showV,
                  fn v => Seq.length (Seq.map (fn x => x) v) = Seq.length v),

        P.forAll ("mapi with the index ignored is map", genV, showV,
                  fn v =>
                    ints (Seq.mapi (fn (_, x) => x) v) = ints (Seq.map (fn x => x) v)),

        P.forAll ("concat is additive over lengths",
                  G.list genV, Show.list showV,
                  fn vs =>
                    Seq.length (Seq.concat vs)
                    = List.foldl (fn (v, a) => a + Seq.length v) 0 vs),

        P.forAll ("foldri sees every index in order", genV, showV,
                  fn v =>
                    Seq.foldri (fn (i, _, a) => i :: a) [] v
                    = List.tabulate (Seq.length v, fn i => i)),

        P.forAll ("exists is the dual of all", genV, showV,
                  fn v =>
                    Seq.exists (fn x => toInt x > 100) v
                    = not (Seq.all (fn x => toInt x <= 100) v)),

        P.forAll ("collate agrees with List.collate",
                  G.pair (genV, genV), Show.pair (showV, showV),
                  fn (a, b) =>
                    Seq.collate cmp (a, b)
                    = List.collate Int.compare (ints a, ints b))
      ])
  end

functor MonoArrayTestsFn (structure Seq : MONO_ARRAY
                          val name : string
                          val elem : int -> Seq.elem
                          val toInt : Seq.elem -> int
                          val vectorToInts : Seq.vector -> int list) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    fun ints a = List.map toInt (Seq.foldr (op ::) [] a)
    fun ofInts ns = Seq.fromList (List.map elem ns)
    val showA = fn a => Show.intList (ints a)
    fun cmp (x, y) = Int.compare (toInt x, toInt y)

    val genInts = G.list (G.int (0, 255))

    val withIndex =
      G.bind (G.filter (fn ns => not (List.null ns)) genInts) (fn ns =>
        G.map (fn i => (ns, i)) (G.int (0, List.length ns - 1)))
    val showWithIndex = Show.pair (Show.intList, Show.int)

    val suite = Group (name,
      [ Case ("construction", fn () =>
          (A.that "maxLen is non-negative" (Seq.maxLen >= 0);
           A.eqIntList "array fills" ([7, 7, 7], ints (Seq.array (3, elem 7)));
           A.eqIntList "fromList" ([1, 2, 3], ints (ofInts [1, 2, 3]));
           A.eqIntList "tabulate"
             ([0, 2, 4], ints (Seq.tabulate (3, fn i => elem (i * 2))));
           A.eqInt "length" (3, Seq.length (ofInts [1, 2, 3]));
           A.raises "negative length" A.isSize
             (fn () => Seq.array (A.hide ~1, elem 0));
           A.raises "negative tabulate" A.isSize
             (fn () => Seq.tabulate (A.hide ~1, fn _ => elem 0)))),

        Case ("sub, update and vector", fn () =>
          let val a = ofInts [1, 2, 3]
          in
            A.eqInt "sub" (2, toInt (Seq.sub (a, 1)));
            Seq.update (a, 1, elem 9);
            A.eqInt "after update" (9, toInt (Seq.sub (a, 1)));
            A.eqIntList "the rest is untouched" ([1, 9, 3], ints a);
            A.eqIntList "vector takes a snapshot"
              ([1, 9, 3], vectorToInts (Seq.vector a));
            A.raises "sub past the end" A.isSubscript
              (fn () => Seq.sub (a, A.hide 3));
            A.raises "sub negative" A.isSubscript
              (fn () => Seq.sub (a, A.hide ~1));
            A.raises "update past the end" A.isSubscript
              (fn () => Seq.update (a, A.hide 3, elem 0))
          end),

        Case ("copy and copyVec", fn () =>
          let
            val dst = Seq.array (4, elem 0)
          in
            Seq.copy { src = ofInts [1, 2], dst = dst, di = 1 };
            A.eqIntList "copy" ([0, 1, 2, 0], ints dst);
            Seq.copyVec { src = Seq.vector (ofInts [5]), dst = dst, di = 3 };
            A.eqIntList "copyVec" ([0, 1, 2, 5], ints dst);
            A.raises "past the end" A.isSubscript
              (fn () => Seq.copy { src = ofInts [1, 2], dst = dst, di = 3 });
            A.raises "negative offset" A.isSubscript
              (fn () => Seq.copy { src = ofInts [1], dst = dst, di = A.hide ~1 })
          end),

        Case ("copying onto itself changes nothing", fn () =>
          let val a = ofInts [1, 2, 3, 4, 5]
          in
            Seq.copy { src = a, dst = a, di = 0 };
            A.eqIntList "unchanged" ([1, 2, 3, 4, 5], ints a)
          end),

        Case ("app, appi, modify and modifyi", fn () =>
          let
            val a = ofInts [1, 2, 3]
            val seen = ref []
          in
            Seq.app (fn x => seen := toInt x :: !seen) a;
            A.eqIntList "app" ([3, 2, 1], !seen);
            seen := [];
            Seq.appi (fn (i, x) => seen := (i * 100 + toInt x) :: !seen) a;
            A.eqIntList "appi" ([203, 102, 1], !seen);
            Seq.modify (fn x => elem (toInt x * 2)) a;
            A.eqIntList "modify" ([2, 4, 6], ints a);
            Seq.modifyi (fn (i, x) => elem (toInt x + i)) a;
            A.eqIntList "modifyi" ([2, 5, 8], ints a)
          end),

        Case ("the folds", fn () =>
          let val a = ofInts [1, 2, 3]
          in
            A.eqIntList "foldl" ([3, 2, 1], Seq.foldl (fn (x, l) => toInt x :: l) [] a);
            A.eqIntList "foldr" ([1, 2, 3], Seq.foldr (fn (x, l) => toInt x :: l) [] a);
            A.eqIntList "foldli" ([2, 1, 0], Seq.foldli (fn (i, _, l) => i :: l) [] a);
            A.eqIntList "foldri" ([0, 1, 2], Seq.foldri (fn (i, _, l) => i :: l) [] a)
          end),

        Case ("searching and collate", fn () =>
          let val a = ofInts [1, 2, 3, 4]
          in
            A.eqIntOption "find"
              (SOME 2, Option.map toInt (Seq.find (fn x => toInt x mod 2 = 0) a));
            A.eqBy (op =, Show.option (Show.pair (Show.int, Show.int)))
              "findi" (SOME (1, 2),
                       Option.map (fn (i, x) => (i, toInt x))
                                  (Seq.findi (fn (_, x) => toInt x mod 2 = 0) a));
            A.eqBool "exists" (true, Seq.exists (fn x => toInt x = 3) a);
            A.eqBool "all" (true, Seq.all (fn x => toInt x > 0) a);
            A.eqOrder "collate a prefix"
              (LESS, Seq.collate cmp (ofInts [1], ofInts [1, 2]))
          end),

        Case ("arrays are compared by identity", fn () =>
          let
            val a = ofInts [1, 2, 3]
            val b = ofInts [1, 2, 3]
          in
            A.that "an array is equal to itself" (a = a);
            A.that "distinct arrays with equal contents differ" (a <> b)
          end),

        P.forAll ("fromList and the fold are inverse", genInts, Show.intList,
                  fn ns => ints (ofInts ns) = ns),

        P.forAll ("sub after update returns what was written",
                  withIndex, showWithIndex,
                  fn (ns, i) =>
                    let val a = ofInts ns
                    in Seq.update (a, i, elem 99); toInt (Seq.sub (a, i)) = 99 end),

        P.forAll ("update leaves every other position alone",
                  withIndex, showWithIndex,
                  fn (ns, i) =>
                    let
                      val a = ofInts ns
                      val () = Seq.update (a, i, elem 99)
                    in
                      Seq.foldli (fn (j, x, acc) =>
                                  acc andalso (j = i orelse toInt x = List.nth (ns, j)))
                               true a
                    end),

        P.forAll ("modify is map in place", genInts, Show.intList,
                  fn ns =>
                    let val a = ofInts ns
                    in
                      Seq.modify (fn x => elem ((toInt x + 1) mod 256)) a;
                      ints a = List.map (fn n => (n + 1) mod 256) ns
                    end),

        P.forAll ("copying onto a fresh array preserves the contents",
                  genInts, Show.intList,
                  fn ns =>
                    let
                      val src = ofInts ns
                      val dst = Seq.array (List.length ns, elem 0)
                    in
                      Seq.copy { src = src, dst = dst, di = 0 };
                      ints dst = ns
                    end),

        P.forAll ("vector round trips the contents", genInts, Show.intList,
                  fn ns => vectorToInts (Seq.vector (ofInts ns)) = ns),

        P.forAll ("collate agrees with List.collate",
                  G.pair (genInts, genInts),
                  Show.pair (Show.intList, Show.intList),
                  fn (xs, ys) =>
                    Seq.collate cmp (ofInts xs, ofInts ys)
                    = List.collate Int.compare (xs, ys))
      ])
  end
