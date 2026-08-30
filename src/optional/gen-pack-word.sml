(* Generic tests for PACK_WORD, instantiated for every PackWordNBig and
 * PackWordNLittle structure an implementation provides.
 *
 * These structures are optional, so this file is only reached through a build
 * description that names them; see build/optional/.
 *
 * Nothing here hard-codes a width.  `bytesPerElem` is read from the structure
 * and every boundary value is derived from it, so the same body tests
 * PackWord16Big and PackWord64Little.  What *is* declared at the
 * instantiation site is the endianness the structure's name promises: that is
 * the one fact the structure cannot be trusted to report about itself, since
 * `isBigEndian` is exactly what a byte-order bug would get wrong.
 *)

functor PackWordTestsFn (structure Pack : PACK_WORD
                         val name : string
                         val bigEndian : bool) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure LW = LargeWord
    structure W8 = Word8
    structure W8V = Word8Vector
    structure W8A = Word8Array

    val n = Pack.bytesPerElem
    val bits = 8 * n

    val zero = LW.fromInt 0
    val one = LW.fromInt 1
    val allOnes = LW.notb zero

    (* The mask of one element's width.  Shifting a word by its own width is
     * defined to yield zero, but only for `<<` and `>>`; building the mask by
     * shifting past the end would work, yet writing the wide case out
     * separately says plainly that an element may be as wide as LargeWord. *)
    val mask =
      if bits >= LW.wordSize then allOnes
      else LW.- (LW.<< (one, Word.fromInt bits), one)

    fun maskOf w = LW.andb (w, mask)

    (* Sign extension from the element width to the full LargeWord width, which
     * is what subVecX and subArrX are specified to do. *)
    fun signExtend w =
      if bits >= LW.wordSize then w
      else if LW.andb (w, LW.<< (one, Word.fromInt (bits - 1))) = zero then w
      else LW.orb (w, LW.notb mask)

    fun showLW w = "0wx" ^ LW.toString w
    val eqLW = A.eqBy (op =, showLW)

    (* One element's bytes, in memory order, assembled into the word the
     * structure should report. *)
    fun elemOf bytes =
      List.foldl (fn (b, acc) => LW.orb (LW.<< (acc, 0w8), W8.toLarge b))
                 zero
                 (if bigEndian then bytes else List.rev bytes)

    (* The inverse: the bytes, in memory order, of the low `bits` of w. *)
    fun bytesOfElem w =
      let
        val big =
          List.tabulate (n, fn k =>
            W8.fromLarge (LW.>> (w, Word.fromInt (8 * (n - 1 - k)))))
      in
        if bigEndian then big else List.rev big
      end

    fun vec ns = W8V.fromList (List.map W8.fromInt ns)
    fun arr ns = W8A.fromList (List.map W8.fromInt ns)
    fun vlist v = W8V.foldr (op ::) [] v
    fun alist a = W8A.foldr (op ::) [] a
    val showBytes = Show.list (fn b => "0wx" ^ W8.toString b)
    val eqBytes = A.eqBy (op =, showBytes)

    (* A distinguishable pattern: byte k is k + 1, so a byte-order mistake
     * shows up as a different number rather than the same one. *)
    val ramp = List.tabulate (n, fn k => k + 1)
    val rampWord = elemOf (List.map W8.fromInt ramp)
    val high = List.tabulate (n, fn _ => 255)

    (* --- generators --------------------------------------------------- *)

    val genByte = G.int (0, 255)
    val genElem = G.listN n genByte

    (* k elements' worth of bytes, an index into them, and a replacement
     * element: enough for every update law in one shape. *)
    val genUpdate =
      G.bind (G.int (1, 5)) (fn k =>
        G.bind (G.listN (k * n) genByte) (fn bs =>
          G.bind (G.int (0, k - 1)) (fn idx =>
            G.map (fn nb => (bs, idx, nb)) genElem)))
    val showUpdate = Show.triple (Show.intList, Show.int, Show.intList)

    val genRead =
      G.bind (G.int (1, 5)) (fn k =>
        G.bind (G.listN (k * n) genByte) (fn bs =>
          G.map (fn idx => (bs, idx)) (G.int (0, k - 1))))
    val showRead = Show.pair (Show.intList, Show.int)

    fun nth (bs, idx) =
      List.map W8.fromInt
        (List.take (List.drop (bs, idx * n), n))

    val suite = Group (name,
      [ Case ("element size and byte order", fn () =>
          (A.that "bytesPerElem is positive" (n > 0);
           A.that "an element fits in a LargeWord" (bits <= LW.wordSize);
           A.eqBool ("isBigEndian agrees with the name " ^ name)
             (bigEndian, Pack.isBigEndian))),

        Case ("subVec assembles the bytes in the declared order", fn () =>
          (eqLW "a ramp" (rampWord, Pack.subVec (vec ramp, 0));
           eqLW "all zero bytes" (zero, Pack.subVec (vec (List.map (fn _ => 0) ramp), 0));
           eqLW "all one bits" (mask, Pack.subVec (vec high, 0)))),

        Case ("the index counts elements, not bytes", fn () =>
          let
            val v = vec (List.map (fn _ => 0) ramp @ ramp)
          in
            eqLW "element zero" (zero, Pack.subVec (v, 0));
            eqLW "element one" (rampWord, Pack.subVec (v, 1))
          end),

        Case ("subVecX sign-extends where subVec zero-extends", fn () =>
          let
            val v = vec high
          in
            eqLW "subVec of an all-ones element" (mask, Pack.subVec (v, 0));
            eqLW "subVecX of an all-ones element" (allOnes, Pack.subVecX (v, 0));
            (* A top byte below 0x80 leaves the sign bit clear, so the two
             * agree.  Byte 0 in memory order is the most significant one only
             * when the structure is big-endian. *)
            let
              val small = if bigEndian then 1 :: List.tl high
                          else List.take (high, n - 1) @ [1]
              val sv = vec small
            in
              eqLW "they agree when the top bit is clear"
                (Pack.subVec (sv, 0), Pack.subVecX (sv, 0))
            end
          end),

        Case ("subArr and subArrX read what subVec reads", fn () =>
          let
            val a = arr ramp
          in
            eqLW "subArr" (Pack.subVec (vec ramp, 0), Pack.subArr (a, 0));
            eqLW "subArrX" (Pack.subVecX (vec ramp, 0), Pack.subArrX (a, 0));
            eqLW "subArr of an all-ones element" (mask, Pack.subArr (arr high, 0));
            eqLW "subArrX of an all-ones element"
              (allOnes, Pack.subArrX (arr high, 0))
          end),

        Case ("reading out of range raises Subscript", fn () =>
          let
            val v = vec ramp
            val a = arr ramp
          in
            A.raises "subVec at a negative index" A.isSubscript
              (fn () => Pack.subVec (v, A.hide ~1));
            A.raises "subVec past the end" A.isSubscript
              (fn () => Pack.subVec (v, A.hide 1));
            A.raises "subVecX at a negative index" A.isSubscript
              (fn () => Pack.subVecX (v, A.hide ~1));
            A.raises "subVecX past the end" A.isSubscript
              (fn () => Pack.subVecX (v, A.hide 1));
            A.raises "subArr at a negative index" A.isSubscript
              (fn () => Pack.subArr (a, A.hide ~1));
            A.raises "subArr past the end" A.isSubscript
              (fn () => Pack.subArr (a, A.hide 1));
            A.raises "subArrX at a negative index" A.isSubscript
              (fn () => Pack.subArrX (a, A.hide ~1));
            A.raises "subArrX past the end" A.isSubscript
              (fn () => Pack.subArrX (a, A.hide 1))
          end),

        Case ("a partial element at the end is not readable", fn () =>
          let
            (* One byte short of a whole element, so index 0 is already out of
             * range even though the sequence is not empty. *)
            val short = List.take (ramp, n - 1)
          in
            if n = 1 then
              (* A one-byte element has no partial case; the empty sequence is
               * the boundary instead. *)
              (A.raises "subVec of an empty vector" A.isSubscript
                 (fn () => Pack.subVec (vec [], A.hide 0));
               A.raises "subArr of an empty array" A.isSubscript
                 (fn () => Pack.subArr (arr [], A.hide 0)))
            else
              (A.raises "subVec" A.isSubscript
                 (fn () => Pack.subVec (vec short, A.hide 0));
               A.raises "subArr" A.isSubscript
                 (fn () => Pack.subArr (arr short, A.hide 0)))
          end),

        Case ("update writes one element's worth of bytes", fn () =>
          let
            val a = arr (List.map (fn _ => 0) (ramp @ ramp))
          in
            Pack.update (a, 1, rampWord);
            eqBytes "the addressed element"
              (List.map W8.fromInt ramp,
               List.take (List.drop (alist a, n), n));
            eqBytes "the untouched element"
              (List.map W8.fromInt (List.map (fn _ => 0) ramp),
               List.take (alist a, n))
          end),

        Case ("update keeps only the low bytes of its argument", fn () =>
          let
            val a = arr (List.map (fn _ => 0) ramp)
          in
            Pack.update (a, 0, allOnes);
            eqLW "an all-ones word narrows to the element width"
              (mask, Pack.subArr (a, 0));
            Pack.update (a, 0, zero);
            eqLW "and back to zero" (zero, Pack.subArr (a, 0))
          end),

        Case ("update out of range raises Subscript", fn () =>
          let
            val a = arr ramp
          in
            A.raises "at a negative index" A.isSubscript
              (fn () => Pack.update (a, A.hide ~1, zero));
            A.raises "past the end" A.isSubscript
              (fn () => Pack.update (a, A.hide 1, zero));
            eqBytes "and the array is unchanged"
              (List.map W8.fromInt ramp, alist a)
          end),

        P.forAll ("subVec agrees with assembling the bytes by hand",
                  genRead, showRead,
                  fn (bs, idx) =>
                    Pack.subVec (vec bs, idx) = elemOf (nth (bs, idx))),

        P.forAll ("subArr agrees with subVec on the same bytes",
                  genRead, showRead,
                  fn (bs, idx) =>
                    Pack.subArr (arr bs, idx) = Pack.subVec (vec bs, idx)),

        P.forAll ("subVecX is subVec sign-extended", genRead, showRead,
                  fn (bs, idx) =>
                    Pack.subVecX (vec bs, idx)
                    = signExtend (Pack.subVec (vec bs, idx))),

        P.forAll ("subArrX is subArr sign-extended", genRead, showRead,
                  fn (bs, idx) =>
                    Pack.subArrX (arr bs, idx)
                    = signExtend (Pack.subArr (arr bs, idx))),

        P.forAll ("the low bits survive update and read back",
                  genUpdate, showUpdate,
                  fn (bs, idx, nb) =>
                    let
                      val a = arr bs
                      val w = elemOf (List.map W8.fromInt nb)
                    in
                      Pack.update (a, idx, w);
                      Pack.subArr (a, idx) = maskOf w
                    end),

        P.forAll ("update writes exactly the bytes of its argument",
                  genUpdate, showUpdate,
                  fn (bs, idx, nb) =>
                    let
                      val a = arr bs
                      val w = elemOf (List.map W8.fromInt nb)
                    in
                      Pack.update (a, idx, w);
                      List.take (List.drop (alist a, idx * n), n)
                      = bytesOfElem w
                    end),

        P.forAll ("update leaves every other element alone",
                  genUpdate, showUpdate,
                  fn (bs, idx, nb) =>
                    let
                      val a = arr bs
                      val original = alist a
                      val w = elemOf (List.map W8.fromInt nb)
                      val after = (Pack.update (a, idx, w); alist a)
                      fun inside k = k >= idx * n andalso k < (idx + 1) * n
                    in
                      List.all
                        (fn k => inside k
                                 orelse List.nth (original, k) = List.nth (after, k))
                        (List.tabulate (List.length original, fn k => k))
                    end),

        P.forAll ("a value narrowed to the element width is a fixed point",
                  genUpdate, showUpdate,
                  fn (bs, idx, nb) =>
                    let
                      val a = arr bs
                      val w = maskOf (elemOf (List.map W8.fromInt nb))
                    in
                      Pack.update (a, idx, w);
                      Pack.subArr (a, idx) = w
                    end)
      ])
  end
