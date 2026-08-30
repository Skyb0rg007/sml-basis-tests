(* Applies the generic signature tests to every required instance.
 *
 * The Basis requires three WORD structures, three INTEGER structures, two REAL
 * structures and eight monomorphic sequence structures.  Each is a separate
 * implementation, so each is tested; the bodies live in gen-mono-seq.sml,
 * gen-mono-slice.sml and gen-numeric.sml.
 *)

functor InstanceTestsFn (C : TEST_CONFIG) =
  struct
    (* --- monomorphic vectors and arrays --- *)

    structure CharVectorT =
      MonoVectorTestsFn (structure Seq = CharVector
                         val name = "CharVector"
                         val elem = Char.chr
                         val toInt = Char.ord)

    structure Word8VectorT =
      MonoVectorTestsFn (structure Seq = Word8Vector
                         val name = "Word8Vector"
                         val elem = Word8.fromInt
                         val toInt = Word8.toInt)

    structure CharArrayT =
      MonoArrayTestsFn (structure Seq = CharArray
                        val name = "CharArray"
                        val elem = Char.chr
                        val toInt = Char.ord
                        val vectorToInts = fn v =>
                          List.map Char.ord (CharVector.foldr (op ::) [] v))

    structure Word8ArrayT =
      MonoArrayTestsFn (structure Seq = Word8Array
                        val name = "Word8Array"
                        val elem = Word8.fromInt
                        val toInt = Word8.toInt
                        val vectorToInts = fn v =>
                          List.map Word8.toInt (Word8Vector.foldr (op ::) [] v))

    (* --- slices --- *)

    structure CharVectorSliceT =
      MonoVectorSliceTestsFn (structure Slice = CharVectorSlice
                              val name = "CharVectorSlice"
                              val elem = Char.chr
                              val toInt = Char.ord
                              val ofInts = fn ns =>
                                CharVector.fromList (List.map Char.chr ns)
                              val vectorToInts = fn v =>
                                List.map Char.ord (CharVector.foldr (op ::) [] v))

    structure Word8VectorSliceT =
      MonoVectorSliceTestsFn (structure Slice = Word8VectorSlice
                              val name = "Word8VectorSlice"
                              val elem = Word8.fromInt
                              val toInt = Word8.toInt
                              val ofInts = fn ns =>
                                Word8Vector.fromList (List.map Word8.fromInt ns)
                              val vectorToInts = fn v =>
                                List.map Word8.toInt
                                         (Word8Vector.foldr (op ::) [] v))

    structure CharArraySliceT =
      MonoArraySliceTestsFn (structure Slice = CharArraySlice
                             val name = "CharArraySlice"
                             val elem = Char.chr
                             val toInt = Char.ord
                             val ofInts = fn ns =>
                               CharArray.fromList (List.map Char.chr ns)
                             val arrayToInts = fn a =>
                               List.map Char.ord (CharArray.foldr (op ::) [] a)
                             val vectorToInts = fn v =>
                               List.map Char.ord (CharVector.foldr (op ::) [] v)
                             val vectorSliceOfInts = fn ns =>
                               CharVectorSlice.full
                                 (CharVector.fromList (List.map Char.chr ns)))

    structure Word8ArraySliceT =
      MonoArraySliceTestsFn (structure Slice = Word8ArraySlice
                             val name = "Word8ArraySlice"
                             val elem = Word8.fromInt
                             val toInt = Word8.toInt
                             val ofInts = fn ns =>
                               Word8Array.fromList (List.map Word8.fromInt ns)
                             val arrayToInts = fn a =>
                               List.map Word8.toInt
                                        (Word8Array.foldr (op ::) [] a)
                             val vectorToInts = fn v =>
                               List.map Word8.toInt
                                        (Word8Vector.foldr (op ::) [] v)
                             val vectorSliceOfInts = fn ns =>
                               Word8VectorSlice.full
                                 (Word8Vector.fromList
                                    (List.map Word8.fromInt ns)))

    (* --- numeric instances --- *)

    structure WordT = WordInstanceTestsFn (structure W = Word
                                           val name = "Word")
    structure Word8T = WordInstanceTestsFn (structure W = Word8
                                            val name = "Word8")
    structure LargeWordT = WordInstanceTestsFn (structure W = LargeWord
                                                val name = "LargeWord")

    structure IntT = IntegerInstanceTestsFn (structure I = Int
                                             val name = "Int")
    structure LargeIntT = IntegerInstanceTestsFn (structure I = LargeInt
                                                  val name = "LargeInt")
    structure PositionT = IntegerInstanceTestsFn (structure I = Position
                                                  val name = "Position")

    structure RealT = RealInstanceTestsFn (structure R = Real
                                           val name = "Real"
                                           val ieee = C.hasIEEEReals)
    structure LargeRealT = RealInstanceTestsFn (structure R = LargeReal
                                                val name = "LargeReal"
                                                val ieee = C.hasIEEEReals)

    val suite =
      Test.Group ("Every required instance",
        [ Test.Group ("monomorphic sequences",
            [ CharVectorT.suite, Word8VectorT.suite
            , CharArrayT.suite, Word8ArrayT.suite
            , CharVectorSliceT.suite, Word8VectorSliceT.suite
            , CharArraySliceT.suite, Word8ArraySliceT.suite ])
        , Test.Group ("words", [WordT.suite, Word8T.suite, LargeWordT.suite])
        , Test.Group ("integers", [IntT.suite, LargeIntT.suite, PositionT.suite])
        , Test.Group ("reals", [RealT.suite, LargeRealT.suite])
        ])
  end
