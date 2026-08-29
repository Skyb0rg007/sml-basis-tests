(* all-tests.sml -- assembles every module's suite under one configuration.
 *
 * Each test module is a functor over TEST_CONFIG, whether or not it currently
 * consults the configuration.  Keeping the shape uniform means a module can
 * start depending on a configuration flag later without any change here.
 *)

functor AllTestsFn (C : TEST_CONFIG) =
  struct
    structure T01 = GeneralTestsFn (C)
    structure T02 = OptionTestsFn (C)
    structure T03 = BoolTestsFn (C)
    structure T04 = ListTestsFn (C)
    structure T05 = ListPairTestsFn (C)
    structure T06 = IntTestsFn (C)
    structure T07 = WordTestsFn (C)
    structure T08 = CharTestsFn (C)
    structure T09 = StringTestsFn (C)
    structure T10 = SubstringTestsFn (C)
    structure T11 = StringCvtTestsFn (C)
    structure T12 = VectorTestsFn (C)
    structure T13 = ArrayTestsFn (C)
    structure T14 = SliceTestsFn (C)
    structure T15 = RealTestsFn (C)
    structure T16 = MathTestsFn (C)
    structure T17 = TimeTestsFn (C)
    structure T18 = OSPathTestsFn (C)
    structure T19 = ByteTestsFn (C)
    structure T20 = TextIOTestsFn (C)
    structure T21 = OSProcessTestsFn (C)

    val suite =
      Test.Group ("Standard ML Basis Library",
        [ T01.suite, T02.suite, T03.suite, T04.suite, T05.suite
        , T06.suite, T07.suite, T08.suite, T09.suite, T10.suite
        , T11.suite, T12.suite, T13.suite, T14.suite, T15.suite
        , T16.suite, T17.suite, T18.suite, T19.suite, T20.suite
        , T21.suite
        ])
  end
