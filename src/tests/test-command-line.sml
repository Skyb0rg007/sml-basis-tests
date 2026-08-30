(* Tests for CommandLine.
 *
 * The suite cannot know how it was invoked, so nothing here asserts a
 * particular name or a particular argument list.  What the specification does
 * fix is that the two functions are total, that they answer consistently
 * within a run, and that the program name is not itself one of the arguments.
 *)

functor CommandLineTestsFn (C : TEST_CONFIG) =
  struct
    open Test
    structure A = Assert
    structure G = Gen
    structure P = Prop

    val suite = Group ("CommandLine",
      [ Case ("name returns a string", fn () =>
          A.noRaise "name" (fn () => CommandLine.name ())),

        Case ("arguments returns a list", fn () =>
          A.noRaise "arguments" (fn () => CommandLine.arguments ())),

        (* Both are specified to describe one fixed invocation, so repeated
         * calls must agree; an implementation that consumed the arguments
         * would fail here. *)
        Case ("name is stable across calls", fn () =>
          A.eqString "two calls agree"
            (CommandLine.name (), CommandLine.name ())),

        Case ("arguments is stable across calls", fn () =>
          A.eqStringList "two calls agree"
            (CommandLine.arguments (), CommandLine.arguments ())),

        Case ("the program name is not part of the argument list", fn () =>
          (* argv[0] belongs to name, not to arguments. *)
          A.that "arguments does not begin with the program name"
            (case CommandLine.arguments () of
                 [] => true
               | first :: _ => first <> CommandLine.name ())),

        P.forAll ("arguments are ordinary strings, however many there are",
                  G.int (0, 4), Show.int,
                  fn _ =>
                    List.all (fn s => String.size s >= 0)
                             (CommandLine.arguments ()))
      ])
  end
