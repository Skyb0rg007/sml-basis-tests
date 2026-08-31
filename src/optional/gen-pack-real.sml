(* Generic tests for PACK_REAL, instantiated for every PackReal pair an
 * implementation provides.
 *
 * The tests take the big-endian and little-endian structures together rather
 * than one at a time.  A single structure cannot be asked whether it got the
 * byte order right without assuming a particular floating point format --
 * "the first byte of 1.0 is 0x3F" is a fact about IEEE 754 binary64, not
 * about PACK_REAL.  The pair can: whatever the format, the two must lay the
 * same value down in opposite orders.  That is checkable, and it is what the
 * signature actually promises.
 *)

functor PackRealTestsFn (structure Big : PACK_REAL
                         structure Little : PACK_REAL
                         structure R : REAL
                         sharing type Big.real = R.real
                         sharing type Little.real = R.real
                         val name : string
                         val ieee : bool) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop
    structure W8 = Word8
    structure W8V = Word8Vector
    structure W8A = Word8Array

    val n = Big.bytesPerElem

    val r = R.fromInt
    fun showR x = R.fmt StringCvt.EXACT x
    fun eqR msg (e, a) =
      if R.== (e, a) then ()
      else A.fail (msg ^ ": expected " ^ showR e ^ " but got " ^ showR a)

    (* Bit-for-bit identity rather than numeric equality, so that ~0.0 and 0.0
     * are told apart and a NaN can be compared with itself at all. *)
    fun sameBytes (x, y) = Big.toBytes x = Big.toBytes y
    fun eqBits msg (e, a) =
      if sameBytes (e, a) then ()
      else A.fail (msg ^ ": expected " ^ showR e ^ " but got " ^ showR a)

    fun vlist v = W8V.foldr (op ::) [] v
    fun alist a = W8A.foldr (op ::) [] a
    val showBytes = Show.list (fn b => "0wx" ^ W8.toString b)
    val eqBytes = A.eqBy (op =, showBytes)
    fun vec bs = W8V.fromList bs
    fun zeros k = W8A.array (k, W8.fromInt 0)

    val genR =
      G.oneOf
        [ G.map (fn k => R./ (r k, r 7)) (G.int (~10000, 10000))
        , G.map (fn k => R.* (r k, r 1000000)) (G.int (~10000, 10000))
        , G.elem [ r 0, R.~ (r 0), r 1, r ~1
                 , R.minPos, R.minNormalPos, R.maxFinite ]
        ]

    val genPair = G.pair (genR, genR)
    val showPair = Show.pair (showR, showR)

    val specials =
      if ieee
      then [ ("infinity", R.posInf), ("negative infinity", R.negInf)
           , ("negative zero", R.~ (r 0)) ]
      else []

    val suite = Group (name,
      [ Case ("element size and byte order", fn () =>
          (A.that "bytesPerElem is positive" (n > 0);
           A.eqInt "both orders use the same element size"
             (n, Little.bytesPerElem);
           A.eqBool "the big-endian structure says so" (true, Big.isBigEndian);
           A.eqBool "the little-endian structure says so"
             (false, Little.isBigEndian))),

        Case ("toBytes produces exactly one element's worth", fn () =>
          (A.eqInt "big-endian" (n, W8V.length (Big.toBytes (r 1)));
           A.eqInt "little-endian" (n, W8V.length (Little.toBytes (r 1))))),

        Case ("the two orders are reverses of each other", fn () =>
          let
            (* 1.0 has an asymmetric representation in every format worth
             * testing, so reversal is visible rather than vacuous. *)
            val b = vlist (Big.toBytes (r 1))
            val l = vlist (Little.toBytes (r 1))
          in
            eqBytes "little-endian is the big-endian bytes reversed"
              (List.rev b, l);
            A.falsehood "and the two are not simply equal" (b = l)
          end),

        Case ("fromBytes inverts toBytes", fn () =>
          (eqR "big-endian" (r 42, Big.fromBytes (Big.toBytes (r 42)));
           eqR "little-endian" (r 42, Little.fromBytes (Little.toBytes (r 42)));
           eqR "a fraction"
             (R./ (r 1, r 4), Big.fromBytes (Big.toBytes (R./ (r 1, r 4)))))),

        Case ("each order reads what the other wrote, reversed", fn () =>
          let
            val x = R./ (r ~355, r 113)
          in
            eqR "big reads little's bytes reversed"
              (x, Big.fromBytes (vec (List.rev (vlist (Little.toBytes x)))));
            eqR "little reads big's bytes reversed"
              (x, Little.fromBytes (vec (List.rev (vlist (Big.toBytes x)))))
          end),

        Case ("subVec reads element zero of a vector of bytes", fn () =>
          (eqR "big-endian" (r 7, Big.subVec (Big.toBytes (r 7), 0));
           eqR "little-endian" (r 7, Little.subVec (Little.toBytes (r 7), 0)))),

        Case ("the index counts elements, not bytes", fn () =>
          let
            val v = vec (vlist (Big.toBytes (r 3)) @ vlist (Big.toBytes (r 5)))
          in
            eqR "element zero" (r 3, Big.subVec (v, 0));
            eqR "element one" (r 5, Big.subVec (v, 1))
          end),

        Case ("fromBytes ignores anything past the first element", fn () =>
          let
            val v = vec (vlist (Big.toBytes (r 3)) @ vlist (Big.toBytes (r 5)))
          in
            eqR "only the first element is read" (r 3, Big.fromBytes v)
          end),

        Case ("reading out of range raises Subscript", fn () =>
          let
            val v = Big.toBytes (r 1)
            val a = zeros n
          in
            A.raises "subVec at a negative index" A.isSubscript
              (fn () => Big.subVec (v, A.hide ~1));
            A.raises "subVec past the end" A.isSubscript
              (fn () => Big.subVec (v, A.hide 1));
            A.raises "subArr at a negative index" A.isSubscript
              (fn () => Big.subArr (a, A.hide ~1));
            A.raises "subArr past the end" A.isSubscript
              (fn () => Big.subArr (a, A.hide 1));
            A.raises "fromBytes of too few bytes" A.isSubscript
              (fn () => Big.fromBytes (vec (List.tl (vlist v))))
          end),

        Case ("update writes one element and leaves the next alone", fn () =>
          let
            val a = zeros (2 * n)
          in
            Big.update (a, 1, r 9);
            eqR "the addressed element" (r 9, Big.subArr (a, 1));
            eqBytes "the untouched element"
              (List.tabulate (n, fn _ => W8.fromInt 0),
               List.take (alist a, n));
            Big.update (a, 0, r ~9);
            eqR "the other element, written afterwards" (r ~9, Big.subArr (a, 0));
            eqR "and the first one still holds" (r 9, Big.subArr (a, 1))
          end),

        (* "bytesPerElem: The number of bytes per element, sufficient to
         * store a value of type real." *)
        Case ("an element is wide enough for the real it holds", fn () =>
          A.that ("bytesPerElem = " ^ Int.toString n
                  ^ " must cover R.precision = " ^ Int.toString R.precision)
                 (8 * n >= R.precision)),

        Case ("a partial element cannot be read", fn () =>
          let
            val short = W8V.fromList (List.tl (vlist (Big.toBytes (r 1))))
            val shortArr = zeros (n - 1)
          in
            A.raises "subVec of a short vector" A.isSubscript
              (fn () => Big.subVec (short, A.hide 0));
            A.raises "subArr of a short array" A.isSubscript
              (fn () => Big.subArr (shortArr, A.hide 0));
            A.raises "update into a short array" A.isSubscript
              (fn () => Big.update (shortArr, A.hide 0, r 1))
          end),

        Case ("update out of range raises Subscript", fn () =>
          let
            val a = zeros n
          in
            A.raises "at a negative index" A.isSubscript
              (fn () => Big.update (a, A.hide ~1, r 1));
            A.raises "past the end" A.isSubscript
              (fn () => Big.update (a, A.hide 1, r 1))
          end),

        Case ("the extreme finite values round trip", fn () =>
          (eqBits "maxFinite" (R.maxFinite, Big.fromBytes (Big.toBytes R.maxFinite));
           eqBits "minPos" (R.minPos, Big.fromBytes (Big.toBytes R.minPos));
           eqBits "minNormalPos"
             (R.minNormalPos, Big.fromBytes (Big.toBytes R.minNormalPos));
           eqBits "the most negative finite value"
             (R.~ R.maxFinite,
              Little.fromBytes (Little.toBytes (R.~ R.maxFinite))))),

        (case specials of
             [] => Skip ("the special values round trip",
                         "the configuration declares no IEEE special values")
           | _ =>
             Case ("the special values round trip", fn () =>
               (List.app
                  (fn (why, x) =>
                     eqBits why (x, Big.fromBytes (Big.toBytes x)))
                  specials;
                let
                  val nan = R./ (r 0, r 0)
                in
                  A.that "a NaN is still a NaN afterwards"
                    (R.isNan (Big.fromBytes (Big.toBytes nan)));
                  A.that "and through the little-endian structure too"
                    (R.isNan (Little.fromBytes (Little.toBytes nan)))
                end))),

        P.forAll ("fromBytes inverts toBytes, big-endian", genR, showR,
                  fn x => sameBytes (x, Big.fromBytes (Big.toBytes x))),

        P.forAll ("fromBytes inverts toBytes, little-endian", genR, showR,
                  fn x => sameBytes (x, Little.fromBytes (Little.toBytes x))),

        P.forAll ("the two orders lay the same value down reversed",
                  genR, showR,
                  fn x =>
                    vlist (Little.toBytes x) = List.rev (vlist (Big.toBytes x))),

        P.forAll ("toBytes always yields bytesPerElem bytes", genR, showR,
                  fn x => W8V.length (Big.toBytes x) = n
                          andalso W8V.length (Little.toBytes x) = n),

        P.forAll ("distinct values have distinct bytes", genPair, showPair,
                  fn (x, y) =>
                    Prop.implies (not (R.== (x, y)) andalso not (R.isNan x)
                                  andalso not (R.isNan y),
                                  Big.toBytes x <> Big.toBytes y)),

        P.forAll ("update then subArr round-trips", genPair, showPair,
                  fn (x, y) =>
                    let
                      val a = zeros (2 * n)
                      val b = zeros (2 * n)
                    in
                      Big.update (a, 0, x);
                      Big.update (a, 1, y);
                      Little.update (b, 0, x);
                      Little.update (b, 1, y);
                      sameBytes (x, Big.subArr (a, 0))
                      andalso sameBytes (y, Big.subArr (a, 1))
                      andalso sameBytes (x, Little.subArr (b, 0))
                      andalso sameBytes (y, Little.subArr (b, 1))
                    end),

        P.forAll ("subVec reads back what update wrote", genPair, showPair,
                  fn (x, y) =>
                    let
                      val a = zeros (2 * n)
                    in
                      Little.update (a, 0, x);
                      Little.update (a, 1, y);
                      sameBytes (y,
                        Little.subVec (W8V.fromList (alist a), 1))
                    end)
      ])
  end
