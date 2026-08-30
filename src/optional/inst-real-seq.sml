(* The generic monomorphic sequence tests applied to the real sequences.
 *
 * RealVector, RealArray and their slices are optional, so this file is only
 * reached through a build description that names them; see build/optional/.
 *
 * The generic bodies compare elements by converting them to int, and the
 * values they generate are the whole numbers 0 to 255, which every real
 * format represents exactly.  So `trunc` is an exact inverse of `fromInt`
 * here, and nothing in these tests depends on rounding.
 *)

structure RealSeqTests =
  struct

    structure RealVectorT =
      MonoVectorTestsFn (structure Seq = RealVector
                         val name = "RealVector"
                         val elem = Real.fromInt
                         val toInt = Real.trunc)

    structure RealArrayT =
      MonoArrayTestsFn (structure Seq = RealArray
                        val name = "RealArray"
                        val elem = Real.fromInt
                        val toInt = Real.trunc
                        val vectorToInts = fn v =>
                          List.map Real.trunc (RealVector.foldr (op ::) [] v))

    structure RealVectorSliceT =
      MonoVectorSliceTestsFn (structure Slice = RealVectorSlice
                              val name = "RealVectorSlice"
                              val elem = Real.fromInt
                              val toInt = Real.trunc
                              val ofInts = fn ns =>
                                RealVector.fromList (List.map Real.fromInt ns)
                              val vectorToInts = fn v =>
                                List.map Real.trunc
                                         (RealVector.foldr (op ::) [] v))

    structure RealArraySliceT =
      MonoArraySliceTestsFn (structure Slice = RealArraySlice
                             val name = "RealArraySlice"
                             val elem = Real.fromInt
                             val toInt = Real.trunc
                             val ofInts = fn ns =>
                               RealArray.fromList (List.map Real.fromInt ns)
                             val arrayToInts = fn a =>
                               List.map Real.trunc
                                        (RealArray.foldr (op ::) [] a)
                             val vectorToInts = fn v =>
                               List.map Real.trunc
                                        (RealVector.foldr (op ::) [] v)
                             val vectorSliceOfInts = fn ns =>
                               RealVectorSlice.full
                                 (RealVector.fromList
                                    (List.map Real.fromInt ns)))

    val suites =
      [ RealVectorT.suite, RealArrayT.suite
      , RealVectorSliceT.suite, RealArraySliceT.suite ]

  end
