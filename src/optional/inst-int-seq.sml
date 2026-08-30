(* The generic monomorphic sequence tests applied to the int sequences.
 *
 * IntVector, IntArray and their slices are optional, so this file is only
 * reached through a build description that names them; see build/optional/.
 * The bodies are the same ones the required Char and Word8 sequences use --
 * this file only supplies the conversions to and from int that let those
 * bodies talk about an abstract element type.
 *)

structure IntSeqTests =
  struct

    structure IntVectorT =
      MonoVectorTestsFn (structure Seq = IntVector
                         val name = "IntVector"
                         val elem = fn n => n
                         val toInt = fn n => n)

    structure IntArrayT =
      MonoArrayTestsFn (structure Seq = IntArray
                        val name = "IntArray"
                        val elem = fn n => n
                        val toInt = fn n => n
                        val vectorToInts = fn v =>
                          IntVector.foldr (op ::) [] v)

    structure IntVectorSliceT =
      MonoVectorSliceTestsFn (structure Slice = IntVectorSlice
                              val name = "IntVectorSlice"
                              val elem = fn n => n
                              val toInt = fn n => n
                              val ofInts = fn ns => IntVector.fromList ns
                              val vectorToInts = fn v =>
                                IntVector.foldr (op ::) [] v)

    structure IntArraySliceT =
      MonoArraySliceTestsFn (structure Slice = IntArraySlice
                             val name = "IntArraySlice"
                             val elem = fn n => n
                             val toInt = fn n => n
                             val ofInts = fn ns => IntArray.fromList ns
                             val arrayToInts = fn a =>
                               IntArray.foldr (op ::) [] a
                             val vectorToInts = fn v =>
                               IntVector.foldr (op ::) [] v
                             val vectorSliceOfInts = fn ns =>
                               IntVectorSlice.full (IntVector.fromList ns))

    val suites =
      [ IntVectorT.suite, IntArrayT.suite
      , IntVectorSliceT.suite, IntArraySliceT.suite ]

  end
