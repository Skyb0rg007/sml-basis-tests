(* Tests for Byte, Word8Vector and Word8Array.
 *
 * These are the monomorphic sequence structures, and the point of testing
 * them separately from Vector and Array is that they are separate
 * implementations in most systems -- often hand-written for speed -- rather
 * than instances of the polymorphic ones.
 *)

functor ByteTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure W8 = Word8
    structure W8V = Word8Vector
    structure W8A = Word8Array

    val b = W8.fromInt
    fun showB w = "0wx" ^ W8.toString w
    val showBL = Show.list showB
    val eqBL = A.eqBy (op =, showBL)
    val eqB = A.eqBy (op =, showB)

    fun vlist v = W8V.foldr (op ::) [] v
    fun alist a = W8A.foldr (op ::) [] a

    val bytes = G.map (fn xs => W8V.fromList (List.map b xs))
                      (G.list (G.int (0, 255)))
    fun showBytes v = showBL (vlist v)

    val str = G.asciiString
    val showS = Show.string

    val vecAndIndex =
      G.bind (G.filter (fn v => W8V.length v > 0) bytes) (fn v =>
        G.map (fn i => (v, i)) (G.int (0, W8V.length v - 1)))
    val showVecAndIndex = Show.pair (showBytes, Show.int)

    val suite = Group ("Byte and Word8 sequences",
      [ Group ("Byte",
        [ Case ("charToByte and byteToChar", fn () =>
            (eqB "A" (b 65, Byte.charToByte #"A");
             A.eqChar "back again" (#"A", Byte.byteToChar (b 65));
             eqB "nul" (b 0, Byte.charToByte (Char.chr 0)))),

          Case ("stringToBytes and bytesToString", fn () =>
            (eqBL "bytes of AB"
               ([b 65, b 66], vlist (Byte.stringToBytes "AB"));
             A.eqString "back again"
               ("AB", Byte.bytesToString (W8V.fromList [b 65, b 66]));
             A.eqString "empty" ("", Byte.bytesToString (W8V.fromList [])))),

          Case ("unpackStringVec reads a whole slice", fn () =>
            A.eqString "middle"
              ("BC",
               Byte.unpackStringVec
                 (Word8VectorSlice.slice (Byte.stringToBytes "ABCD", 1, SOME 2)))),

          Case ("unpackString reads from an array", fn () =>
            let
              val a = Byte.stringToBytes "ABCD"
              val arr = W8A.tabulate (4, fn i => W8V.sub (a, i))
            in
              A.eqString "middle"
                ("BC", Byte.unpackString (Word8ArraySlice.slice (arr, 1, SOME 2)))
            end),

          Case ("packString writes into an array", fn () =>
            let
              val arr = W8A.array (4, b 0)
            in
              Byte.packString (arr, 1, Substring.full "AB");
              eqBL "written at the offset"
                ([b 0, b 65, b 66, b 0], alist arr)
            end),

          (* "It raises Subscript if i < 0 or size s + i > |arr|." *)
          Case ("packString checks its bounds", fn () =>
            let
              val arr = W8A.array (4, b 0)
            in
              A.raises "negative offset" A.isSubscript
                (fn () => Byte.packString (arr, A.hide ~1, Substring.full "A"));
              A.raises "past the end" A.isSubscript
                (fn () => Byte.packString (arr, A.hide 3, Substring.full "AB"));
              A.noRaise "exactly filling the array"
                (fn () => Byte.packString (arr, 0, Substring.full "ABCD"));
              A.noRaise "an empty substring at the very end"
                (fn () => Byte.packString (arr, 4, Substring.full ""))
            end),

          (* "unpackStringVec slice returns the string consisting of
           * characters whose codes are held in the vector slice." *)
          Case ("unpacking a whole sequence is bytesToString", fn () =>
            let
              val v = Byte.stringToBytes "ABCD"
              val arr = W8A.tabulate (4, fn i => W8V.sub (v, i))
            in
              A.eqString "the vector slice"
                (Byte.bytesToString v,
                 Byte.unpackStringVec (Word8VectorSlice.full v));
              A.eqString "the array slice"
                (Byte.bytesToString v,
                 Byte.unpackString (Word8ArraySlice.full arr))
            end)
        ]),

        Group ("Word8Vector",
        [ Case ("construction", fn () =>
            (A.eqInt "length" (3, W8V.length (W8V.fromList [b 1, b 2, b 3]));
             eqBL "tabulate"
               ([b 0, b 1, b 2], vlist (W8V.tabulate (3, fn i => b i)));
             A.raises "negative tabulate" A.isSize
               (fn () => W8V.tabulate (A.hide ~1, fn i => b i));
             A.that "maxLen is non-negative" (W8V.maxLen >= 0))),

          Case ("sub", fn () =>
            let
              val v = W8V.fromList [b 1, b 2, b 3]
            in
              eqB "first" (b 1, W8V.sub (v, 0));
              A.raises "past the end" A.isSubscript (fn () => W8V.sub (v, A.hide 3));
              A.raises "negative" A.isSubscript (fn () => W8V.sub (v, A.hide ~1))
            end),

          Case ("update leaves the original alone", fn () =>
            let
              val v = W8V.fromList [b 1, b 2, b 3]
              val v' = W8V.update (v, 1, b 9)
            in
              eqBL "updated" ([b 1, b 9, b 3], vlist v');
              eqBL "original" ([b 1, b 2, b 3], vlist v)
            end),

          Case ("concat, map and the folds", fn () =>
            let
              val v = W8V.fromList [b 1, b 2, b 3]
            in
              eqBL "concat"
                ([b 1, b 2, b 3],
                 vlist (W8V.concat [W8V.fromList [b 1], W8V.fromList [b 2, b 3]]));
              eqBL "map" ([b 2, b 4, b 6], vlist (W8V.map (fn x => x * b 2) v));
              eqBL "foldr rebuilds" ([b 1, b 2, b 3], W8V.foldr op:: [] v);
              eqBL "foldl reverses" ([b 3, b 2, b 1], W8V.foldl op:: [] v);
              A.eqIntList "foldli indices"
                ([2, 1, 0], W8V.foldli (fn (i, _, acc) => i :: acc) [] v)
            end),

          Case ("find, exists, all and collate", fn () =>
            let
              val v = W8V.fromList [b 1, b 2, b 3]
            in
              A.eqBy (op =, Show.option showB) "find"
                (SOME (b 2), W8V.find (fn x => x = b 2) v);
              A.eqBool "exists" (true, W8V.exists (fn x => x = b 3) v);
              A.eqBool "all" (true, W8V.all (fn x => W8.< (x, b 4)) v);
              A.eqOrder "collate" (LESS,
                W8V.collate W8.compare (W8V.fromList [b 1],
                                        W8V.fromList [b 1, b 2]))
            end)
        ]),

        Group ("Word8Array",
        [ Case ("array, sub and update", fn () =>
            let
              val a = W8A.array (3, b 7)
            in
              eqBL "filled" ([b 7, b 7, b 7], alist a);
              W8A.update (a, 1, b 9);
              eqB "after update" (b 9, W8A.sub (a, 1));
              A.raises "past the end" A.isSubscript (fn () => W8A.sub (a, A.hide 3));
              A.raises "negative length" A.isSize (fn () => W8A.array (A.hide ~1, b 0))
            end),

          Case ("vector takes a snapshot", fn () =>
            let
              val a = W8A.fromList [b 1, b 2]
              val v = W8A.vector a
            in
              W8A.update (a, 0, b 9);
              eqBL "the snapshot is unchanged" ([b 1, b 2], vlist v)
            end),

          Case ("copy and copyVec", fn () =>
            let
              val dst = W8A.array (4, b 0)
            in
              W8A.copy { src = W8A.fromList [b 1, b 2], dst = dst, di = 1 };
              eqBL "copy" ([b 0, b 1, b 2, b 0], alist dst);
              W8A.copyVec { src = W8V.fromList [b 5], dst = dst, di = 3 };
              eqBL "copyVec" ([b 0, b 1, b 2, b 5], alist dst);
              A.raises "past the end" A.isSubscript
                (fn () => W8A.copyVec { src = W8V.fromList [b 1, b 2],
                                        dst = dst, di = 3 })
            end),

          Case ("modify", fn () =>
            let
              val a = W8A.fromList [b 1, b 2, b 3]
            in
              W8A.modify (fn x => x + b 1) a;
              eqBL "modified" ([b 2, b 3, b 4], alist a)
            end)
        ]),

        Group ("laws",
        [ P.forAll ("byteToChar inverts charToByte", G.char, Show.char,
                    fn c =>
                      P.implies (Char.ord c < 256,
                                 Byte.byteToChar (Byte.charToByte c) = c)),

          P.forAll ("charToByte inverts byteToChar",
                    G.map b (G.int (0, 255)), showB,
                    fn w => Byte.charToByte (Byte.byteToChar w) = w),

          P.forAll ("bytesToString inverts stringToBytes", str, showS,
                    fn s => Byte.bytesToString (Byte.stringToBytes s) = s),

          P.forAll ("the byte encoding is the character ordinals", str, showS,
                    fn s =>
                      List.map W8.toInt (vlist (Byte.stringToBytes s))
                      = List.map Char.ord (String.explode s)),

          P.forAll ("length is preserved by the encoding", str, showS,
                    fn s => W8V.length (Byte.stringToBytes s) = String.size s),

          P.forAll ("fromList and the fold are inverse", bytes, showBytes,
                    fn v => W8V.fromList (vlist v) = v),

          P.forAll ("sub agrees with the list", vecAndIndex, showVecAndIndex,
                    fn (v, i) => W8V.sub (v, i) = List.nth (vlist v, i)),

          P.forAll ("update changes exactly one position",
                    vecAndIndex, showVecAndIndex,
                    fn (v, i) =>
                      let val v' = W8V.update (v, i, b 200)
                      in
                        W8V.sub (v', i) = b 200
                        andalso W8V.length v' = W8V.length v
                        andalso W8V.foldli
                                  (fn (j, x, acc) =>
                                     acc andalso (j = i orelse x = W8V.sub (v, j)))
                                  true v'
                      end),

          P.forAll ("map preserves length", bytes, showBytes,
                    fn v => W8V.length (W8V.map (fn x => x + b 1) v)
                            = W8V.length v),

          P.forAll ("concat is additive over lengths",
                    G.list bytes, Show.list showBytes,
                    fn vs =>
                      W8V.length (W8V.concat vs)
                      = List.foldl (fn (v, a) => a + W8V.length v) 0 vs),

          P.forAll ("an array round trips through a vector", bytes, showBytes,
                    fn v => W8A.vector (W8A.tabulate (W8V.length v,
                                                      fn i => W8V.sub (v, i)))
                            = v),

          P.forAll ("packString and unpackString round trip", str, showS,
                    fn s =>
                      let
                        val a = W8A.array (String.size s, b 0)
                      in
                        Byte.packString (a, 0, Substring.full s);
                        Byte.unpackString (Word8ArraySlice.full a) = s
                      end),

          P.forAll ("collate agrees with List.collate",
                    G.pair (bytes, bytes), Show.pair (showBytes, showBytes),
                    fn (x, y) =>
                      W8V.collate W8.compare (x, y)
                      = List.collate W8.compare (vlist x, vlist y)),

          (* The specification writes the two conversions out as tabulations,
           * "although one expects actual implementations will be more
           * efficient". *)
          P.forAll ("bytesToString is the tabulation the specification gives",
                    bytes, showBytes,
                    fn v =>
                      Byte.bytesToString v
                      = CharVector.tabulate
                          (W8V.length v,
                           fn i => Byte.byteToChar (W8V.sub (v, i)))),

          P.forAll ("stringToBytes is the tabulation the specification gives",
                    str, showS,
                    fn s =>
                      Byte.stringToBytes s
                      = W8V.tabulate (String.size s,
                                      fn i => Byte.charToByte (String.sub (s, i)))),

          P.forAll ("unpacking a slice reads just that window",
                    G.bind str (fn s =>
                      G.bind (G.int (0, String.size s)) (fn i =>
                        G.map (fn n => (s, i, n))
                              (G.int (0, String.size s - i)))),
                    Show.triple (showS, Show.int, Show.int),
                    fn (s, i, n) =>
                      let
                        val v = Byte.stringToBytes s
                        val arr = W8A.tabulate (W8V.length v,
                                                fn k => W8V.sub (v, k))
                        val window = String.substring (s, i, n)
                      in
                        Byte.unpackStringVec (Word8VectorSlice.slice (v, i, SOME n))
                        = window
                        andalso Byte.unpackString
                                  (Word8ArraySlice.slice (arr, i, SOME n))
                                = window
                      end),

          P.forAll ("packString writes the substring at the offset",
                    G.bind str (fn s =>
                      G.map (fn k => (s, k)) (G.int (0, 3))),
                    Show.pair (showS, Show.int),
                    fn (s, k) =>
                      let
                        val a = W8A.array (String.size s + k, b 0)
                      in
                        Byte.packString (a, k, Substring.full s);
                        alist a
                        = List.tabulate (k, fn _ => b 0)
                          @ List.map Byte.charToByte (String.explode s)
                      end)
        ])
      ])
  end
