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
                    = List.collate Int.compare (ints a, ints b)),

        (* "The expression app f vec is equivalent to appi (f o #2) vec", and
         * the same shape of equivalence for map, foldl and foldr. *)
        P.forAll ("the plain traversals are the indexed ones with the index dropped",
                  genV, showV,
                  fn v =>
                    let
                      val seen = ref []
                      val () = Seq.app (fn x => seen := toInt x :: !seen) v
                      val seenI = ref []
                      val () = Seq.appi ((fn x => seenI := toInt x :: !seenI) o #2) v
                      val f = fn (x, acc) => acc ^ Int.toString (toInt x)
                    in
                      !seen = !seenI
                      andalso ints (Seq.map (fn x => x) v)
                              = ints (Seq.mapi #2 v)
                      andalso Seq.foldl f "z" v
                              = Seq.foldli (fn (_, x, acc) => f (x, acc)) "z" v
                      andalso Seq.foldr f "z" v
                              = Seq.foldri (fn (_, x, acc) => f (x, acc)) "z" v
                    end),

        P.forAll ("foldli sees every index in decreasing order", genV, showV,
                  fn v =>
                    Seq.foldli (fn (i, _, a) => i :: a) [] v
                    = List.rev (List.tabulate (Seq.length v, fn i => i))),

        P.forAll ("findi reports the first index satisfying the predicate",
                  genV, showV,
                  fn v =>
                    let
                      val p = fn x => toInt x > 100
                      fun search i =
                        if i >= Seq.length v then NONE
                        else if p (Seq.sub (v, i))
                        then SOME (i, toInt (Seq.sub (v, i)))
                        else search (i + 1)
                    in
                      Option.map (fn (i, x) => (i, toInt x))
                                 (Seq.findi (fn (_, x) => p x) v)
                      = search 0
                    end),

        P.forAll ("find agrees with List.find", genV, showV,
                  fn v =>
                    let val p = fn n => n > 100
                    in
                      Option.map toInt (Seq.find (fn x => p (toInt x)) v)
                      = List.find p (ints v)
                    end),

        (* "It is equivalent to not(exists (not o f) vec)." *)
        P.forAll ("all is the negation of exists over the negated predicate",
                  genV, showV,
                  fn v =>
                    let val p = fn x => toInt x > 100
                    in Seq.all p v = not (Seq.exists (not o p) v) end),

        P.forAll ("concat is the concatenation of the contents",
                  G.list genV, Show.list showV,
                  fn vs =>
                    ints (Seq.concat vs) = List.concat (List.map ints vs)),

        (* "the elements are defined in order of increasing index" *)
        P.forAll ("tabulate applies its function in increasing index order",
                  G.int (0, 20), Show.int,
                  fn n =>
                    let
                      val seen = ref []
                      val v = Seq.tabulate (n, fn i => (seen := i :: !seen; elem i))
                    in
                      List.rev (!seen) = List.tabulate (n, fn i => i)
                      andalso ints v = List.tabulate (n, fn i => i)
                    end),

        (* "This is equivalent to the expression fromList (List.tabulate
         * (n, f))." *)
        P.forAll ("tabulate is fromList of List.tabulate", G.int (0, 20), Show.int,
                  fn n =>
                    ints (Seq.tabulate (n, fn i => elem (i * 2)))
                    = ints (Seq.fromList (List.tabulate (n, fn i => elem (i * 2))))),

        P.forAll ("find, exists and all stop at the first decision",
                  G.int (1, 20), Show.int,
                  fn n =>
                    let
                      val v = Seq.tabulate (n, fn i => elem i)
                      val calls = ref 0
                      val p = fn x => (calls := !calls + 1; toInt x >= 0)
                      val _ = Seq.find p v
                      val found = !calls
                      val () = calls := 0
                      val _ = Seq.exists p v
                      val existed = !calls
                      val () = calls := 0
                      val _ = Seq.all (fn x => (calls := !calls + 1;
                                                toInt x < 0)) v
                    in
                      found = 1 andalso existed = 1 andalso !calls = 1
                    end)
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

        (* "In copy, if dst and src are equal, we must have di = 0 to avoid
         * an exception, and copy is then the identity." *)
        Case ("copying onto itself changes nothing", fn () =>
          let val a = ofInts [1, 2, 3, 4, 5]
          in
            Seq.copy { src = a, dst = a, di = 0 };
            A.eqIntList "unchanged" ([1, 2, 3, 4, 5], ints a);
            A.raises "at any other offset" A.isSubscript
              (fn () => Seq.copy { src = a, dst = a, di = A.hide 1 })
          end),

        Case ("copyVec checks both bounds", fn () =>
          let
            val dst = Seq.array (2, elem 0)
          in
            A.raises "negative offset" A.isSubscript
              (fn () => Seq.copyVec { src = Seq.vector (ofInts [1]),
                                      dst = dst, di = A.hide ~1 });
            A.raises "past the end" A.isSubscript
              (fn () => Seq.copyVec { src = Seq.vector (ofInts [1, 2, 3]),
                                      dst = dst, di = A.hide 0 });
            A.noRaise "an empty source at the far end"
              (fn () => Seq.copyVec { src = Seq.vector (ofInts []),
                                      dst = dst, di = 2 })
          end),

        Case ("tabulate applies its function in increasing index order", fn () =>
          let
            val seen = ref []
            val a = Seq.tabulate (4, fn i => (seen := i :: !seen; elem i))
          in
            A.eqIntList "the order of the calls" ([0, 1, 2, 3], List.rev (!seen));
            A.eqIntList "the result" ([0, 1, 2, 3], ints a)
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

        (* "the result is equivalent to
         *  Vector.tabulate (length arr, fn i => sub (arr, i))" *)
        P.forAll ("vector is the tabulation of the subscripts",
                  genInts, Show.intList,
                  fn ns =>
                    let val a = ofInts ns
                    in
                      vectorToInts (Seq.vector a)
                      = List.tabulate (Seq.length a,
                                       fn i => toInt (Seq.sub (a, i)))
                    end),

        (* "The expression modify f arr is equivalent to
         *  modifyi (f o #2) arr", and the same for app, foldl and foldr. *)
        P.forAll ("the plain traversals are the indexed ones with the index dropped",
                  genInts, Show.intList,
                  fn ns =>
                    let
                      (* Stays inside the element range for every instance:
                       * a char cannot hold an arbitrary product. *)
                      val f = fn x => elem ((toInt x * 3 + 1) mod 128)
                      val a = ofInts ns
                      val b = ofInts ns
                      val () = Seq.modify f a
                      val () = Seq.modifyi (f o #2) b
                      val c = ofInts ns
                      val g = fn (x, acc) => acc ^ Int.toString (toInt x)
                      val seen = ref []
                      val () = Seq.app (fn x => seen := toInt x :: !seen) c
                      val seenI = ref []
                      val () = Seq.appi ((fn x => seenI := toInt x :: !seenI) o #2) c
                    in
                      ints a = ints b
                      andalso !seen = !seenI
                      andalso Seq.foldl g "z" c
                              = Seq.foldli (fn (_, x, acc) => g (x, acc)) "z" c
                      andalso Seq.foldr g "z" c
                              = Seq.foldri (fn (_, x, acc) => g (x, acc)) "z" c
                    end),

        P.forAll ("the indexed traversals see every index in order",
                  genInts, Show.intList,
                  fn ns =>
                    let
                      val a = ofInts ns
                      val n = List.length ns
                      val seen = ref []
                      val () = Seq.appi (fn (i, _) => seen := i :: !seen) a
                      val touched = ref []
                      val () = Seq.modifyi (fn (i, x) => (touched := i :: !touched; x)) a
                    in
                      List.rev (!seen) = List.tabulate (n, fn i => i)
                      andalso List.rev (!touched) = List.tabulate (n, fn i => i)
                      andalso ints a = ns
                      andalso Seq.foldli (fn (i, _, acc) => i :: acc) [] a
                              = List.rev (List.tabulate (n, fn i => i))
                      andalso Seq.foldri (fn (i, _, acc) => i :: acc) [] a
                              = List.tabulate (n, fn i => i)
                    end),

        P.forAll ("findi reports the first index satisfying the predicate",
                  genInts, Show.intList,
                  fn ns =>
                    let
                      val a = ofInts ns
                      val p = fn n => n > 100
                      fun search i =
                        if i >= List.length ns then NONE
                        else if p (List.nth (ns, i))
                        then SOME (i, List.nth (ns, i))
                        else search (i + 1)
                    in
                      Option.map (fn (i, x) => (i, toInt x))
                                 (Seq.findi (fn (_, x) => p (toInt x)) a)
                      = search 0
                      andalso Option.map toInt (Seq.find (fn x => p (toInt x)) a)
                              = List.find p ns
                      andalso Seq.all (fn x => p (toInt x)) a
                              = not (Seq.exists (fn x => not (p (toInt x))) a)
                    end),

        (* "the i(th) element in src ... being copied to position di + i in
         * the destination array" *)
        P.forAll ("copy and copyVec place the source at the offset",
                  G.bind genInts (fn ns =>
                    G.map (fn k => (ns, k)) (G.int (0, 4))),
                  Show.pair (Show.intList, Show.int),
                  fn (ns, k) =>
                    let
                      val n = List.length ns
                      val dst = Seq.array (n + k, elem 0)
                      val dst2 = Seq.array (n + k, elem 0)
                    in
                      Seq.copy { src = ofInts ns, dst = dst, di = k };
                      Seq.copyVec { src = Seq.vector (ofInts ns),
                                    dst = dst2, di = k };
                      ints dst = List.tabulate (k, fn _ => 0) @ ns
                      andalso ints dst2 = List.tabulate (k, fn _ => 0) @ ns
                    end),

        P.forAll ("collate agrees with List.collate",
                  G.pair (genInts, genInts),
                  Show.pair (Show.intList, Show.intList),
                  fn (xs, ys) =>
                    Seq.collate cmp (ofInts xs, ofInts ys)
                    = List.collate Int.compare (xs, ys))
      ])
  end
