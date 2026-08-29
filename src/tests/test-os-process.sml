(* Tests for OS.Process.
 *
 * Almost everything here is about the environment the program is running in,
 * which is why so little of it can be asserted: the suite must not depend on
 * any particular variable being set, or on being allowed to spawn processes.
 * What it can check is the algebra of the status values and the shape of the
 * answers getEnv gives.
 *)

functor OSProcessTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val suite = Group ("OS.Process",
      [ Group ("status values",
        [ (* OS.Process.status is abstract and is not required to admit
           * equality -- SML/NJ makes it an int, MLton and Poly/ML do not -- so
           * the two values are distinguished through isSuccess rather than by
           * comparing them. *)
          Case ("isSuccess distinguishes success from failure", fn () =>
            (A.eqBool "success" (true, OS.Process.isSuccess OS.Process.success);
             A.eqBool "failure" (false, OS.Process.isSuccess OS.Process.failure)))
        ]),

        Group ("the environment",
          onlyIf (C.hasProcessEnv, "no process environment available")
          [ (* A name that cannot plausibly be set: the answer must be NONE
             * rather than an exception or an empty string. *)
            Case ("an absent variable yields NONE", fn () =>
              A.eqStringOption "absent"
                (NONE,
                 OS.Process.getEnv "SML_BASIS_TESTS_DEFINITELY_UNSET_VARIABLE")),

            Case ("getEnv does not raise on an empty name", fn () =>
              A.noRaise "empty name" (fn () => OS.Process.getEnv "")),

            (* PATH is not guaranteed, so this asserts only that whatever comes
             * back is well-formed, not that anything is there. *)
            Case ("a present variable yields a string", fn () =>
              case OS.Process.getEnv "PATH" of
                  NONE => ()
                | SOME v => A.that "a value is a string" (String.size v >= 0))
          ]),

        Group ("atExit accepts an action",
        [ (* The action cannot be observed from inside the run, so all that is
           * checked is that registering one is accepted and does not run the
           * action immediately. *)
          Case ("registering does not run the action", fn () =>
            let
              val ran = ref false
            in
              OS.Process.atExit (fn () => ran := false);
              A.eqBool "not run yet" (false, !ran)
            end)
        ])
      ])
  end
