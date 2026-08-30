(* The optional structures SML/NJ provides, as of 2026.1.
 *
 * A profile is a declaration, in the same spirit as TEST_CONFIG: what an
 * implementation offers beyond the required Basis cannot be discovered from
 * inside the language, because asking is a compile-time error when the answer
 * is no.  So it is written down, once, per implementation.
 *
 * Adding a structure means one line here and one in build/optional/smlnj.txt.
 * SML/NJ has no Real32, no PackRealBig or PackRealLittle, and no IntVector or
 * IntArray, so those appear in no group below.  It does provide Int63 and
 * Word63, which are the widths of its own default Int and Word and so are
 * already covered by the required-instance tests.
 *)

functor OptionalTestsFn (C : TEST_CONFIG) =
  struct
    (* --- arbitrary precision ------------------------------------------ *)

    structure IntInfT = IntInfTestsFn (C)
    structure IntInfInstanceT =
      IntegerInstanceTestsFn (structure I = IntInf
                              val name = "IntInf as an INTEGER")

    (* --- sized integers ----------------------------------------------- *)

    structure Int32T = IntegerInstanceTestsFn (structure I = Int32
                                               val name = "Int32")
    structure Int64T = IntegerInstanceTestsFn (structure I = Int64
                                               val name = "Int64")
    structure FixedIntT = IntegerInstanceTestsFn (structure I = FixedInt
                                                  val name = "FixedInt")

    (* --- sized words -------------------------------------------------- *)

    structure Word32T = WordInstanceTestsFn (structure W = Word32
                                             val name = "Word32")
    structure Word64T = WordInstanceTestsFn (structure W = Word64
                                             val name = "Word64")
    structure SysWordT = WordInstanceTestsFn (structure W = SysWord
                                              val name = "SysWord")

    (* --- sized reals -------------------------------------------------- *)

    structure Real64T = RealInstanceTestsFn (structure R = Real64
                                             val name = "Real64"
                                             val ieee = C.hasIEEEReals)

    (* --- packing words into byte sequences ---------------------------- *)

    structure PW16B = PackWordTestsFn (structure Pack = PackWord16Big
                                       val name = "PackWord16Big"
                                       val bigEndian = true)
    structure PW16L = PackWordTestsFn (structure Pack = PackWord16Little
                                       val name = "PackWord16Little"
                                       val bigEndian = false)
    structure PW32B = PackWordTestsFn (structure Pack = PackWord32Big
                                       val name = "PackWord32Big"
                                       val bigEndian = true)
    structure PW32L = PackWordTestsFn (structure Pack = PackWord32Little
                                       val name = "PackWord32Little"
                                       val bigEndian = false)
    structure PW64B = PackWordTestsFn (structure Pack = PackWord64Big
                                       val name = "PackWord64Big"
                                       val bigEndian = true)
    structure PW64L = PackWordTestsFn (structure Pack = PackWord64Little
                                       val name = "PackWord64Little"
                                       val bigEndian = false)

    (* --- packing reals into byte sequences ---------------------------- *)

    structure PR64 = PackRealTestsFn (structure Big = PackReal64Big
                                      structure Little = PackReal64Little
                                      structure R = Real64
                                      val name = "PackReal64Big and PackReal64Little"
                                      val ieee = C.hasIEEEReals)

    (* --- two-dimensional arrays --------------------------------------- *)

    structure Array2T = Array2TestsFn (C)

    val suite =
      Test.Group ("Optional structures",
        [ IntInfT.suite, IntInfInstanceT.suite
        , Test.Group ("sized integers",
            [Int32T.suite, Int64T.suite, FixedIntT.suite])
        , Test.Group ("sized words",
            [Word32T.suite, Word64T.suite, SysWordT.suite])
        , Test.Group ("sized reals", [Real64T.suite])
        , Test.Group ("PackWord",
            [ PW16B.suite, PW16L.suite, PW32B.suite, PW32L.suite
            , PW64B.suite, PW64L.suite ])
        , Test.Group ("PackReal", [PR64.suite])
        , Array2T.suite
        , Test.Group ("real sequences", RealSeqTests.suites)
        ])
  end
