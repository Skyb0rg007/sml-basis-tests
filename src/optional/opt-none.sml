(* The optional structures a build covers: none.
 *
 * This is the portable profile, and the one build/sources.cm,
 * build/sources.mlb and build/load.sml use.  Naming a structure the
 * implementation does not provide is a compile-time error rather than
 * something a run-time flag could skip, so a description that must compile
 * everywhere cannot mention any optional structure at all.
 *
 * The group is reported as a skip rather than omitted, for the same reason
 * every other inapplicable test is: a suite that quietly shrinks to nothing
 * still looks green.
 *)

functor OptionalTestsFn (C : TEST_CONFIG) =
  struct
    val suite =
      Test.Group ("Optional structures",
        [ Test.Skip ("(none)",
                     "this build description names no optional structures") ])
  end
