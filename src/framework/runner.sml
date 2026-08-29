(* runner.sml -- walking the test tree and reporting.
 *
 * Each property is seeded from the run seed together with its own fully
 * qualified name.  That makes a property's inputs independent of how many
 * tests happened to run before it, so adding a test earlier in the suite does
 * not silently change the data every later property sees.
 *)

structure Runner =
  struct

    open Test

    type options =
      { seed    : int
      , trials  : int
      , maxSize : int
      , verbose : bool
      , only    : string option
      }

    val defaults : options =
      { seed = 20260101, trials = 100, maxSize = 40, verbose = false, only = NONE }

    type tally = { passed : int, failed : int, errored : int, skipped : int }

    fun say s = (print s; TextIO.flushOut TextIO.stdOut)

    fun join ("", n) = n
      | join (p, n) = p ^ " / " ^ n

    fun indent 0 = ""
      | indent n = "  " ^ indent (n - 1)

    datatype outcome = Ok of Random.rand | Bad of string * string

    fun run (opts : options) suite =
      let
        val { seed, trials, maxSize, verbose, only } = opts

        val passed = ref 0
        val failed = ref 0
        val errored = ref 0
        val skipped = ref 0
        val problems = ref ([] : string list)

        fun selected path =
          case only of
              NONE => true
            | SOME pat => String.isSubstring pat path

        fun anySelected (prefix, Case (n, _)) = selected (join (prefix, n))
          | anySelected (prefix, Prop (n, _)) = selected (join (prefix, n))
          | anySelected (prefix, Skip (n, _)) = selected (join (prefix, n))
          | anySelected (prefix, Group (n, ts)) =
              let val p = join (prefix, n)
              in List.exists (fn t => anySelected (p, t)) ts end

        fun record (depth, name, path, NONE) =
              (passed := !passed + 1;
               if verbose then say (indent depth ^ "ok   " ^ name ^ "\n") else ())
          | record (depth, name, path, SOME (kind, msg)) =
              ((if kind = "FAIL" then failed := !failed + 1
                else errored := !errored + 1);
               problems := (kind ^ "  " ^ path ^ "\n        " ^ msg) :: !problems;
               say (indent depth ^ kind ^ " " ^ name ^ "\n"
                    ^ indent depth ^ "     " ^ msg ^ "\n"))

        fun runCase (depth, name, path, f) =
          record (depth, name, path,
                  ((f (); NONE)
                   handle Assert.TestFail m => SOME ("FAIL", m)
                        | e => SOME ("ERR ", "unexpected exception " ^ exnName e)))

        fun runProp (depth, name, path, f) =
          let
            fun attempt (i, r) =
              (Ok (f (1 + (i mod maxSize)) r))
              handle Assert.TestFail m =>
                       Bad ("FAIL", "trial " ^ Int.toString (i + 1) ^ ": " ^ m)
                   | e =>
                       Bad ("ERR ", "trial " ^ Int.toString (i + 1)
                                    ^ ": unexpected exception " ^ exnName e)
            fun loop (i, r) =
              if i >= trials then NONE
              else case attempt (i, r) of
                       Ok r' => loop (i + 1, r')
                     | Bad x => SOME x
            val start = Random.fromSeedAndName (seed, path)
            val name = name ^ " (" ^ Int.toString trials ^ " trials)"
          in
            record (depth, name, path, loop (0, start))
          end

        fun walk (depth, prefix, t) =
          case t of
              Case (n, f) =>
                let val p = join (prefix, n)
                in if selected p then runCase (depth, n, p, f) else () end
            | Prop (n, f) =>
                let val p = join (prefix, n)
                in if selected p then runProp (depth, n, p, f) else () end
            | Skip (n, why) =>
                let val p = join (prefix, n)
                in
                  if selected p then
                    (skipped := !skipped + 1;
                     say (indent depth ^ "skip " ^ n ^ "  (" ^ why ^ ")\n"))
                  else ()
                end
            | Group (n, ts) =>
                let val p = join (prefix, n)
                in
                  if anySelected (prefix, t) then
                    (say (indent depth ^ n ^ "\n");
                     List.app (fn t => walk (depth + 1, p, t)) ts)
                  else ()
                end
      in
        walk (0, "", suite);
        say "\n";
        (case List.rev (!problems) of
             [] => ()
           | ps => (say "--- failures ------------------------------------------\n";
                    List.app (fn p => say (p ^ "\n")) ps;
                    say "\n"));
        say ("passed " ^ Int.toString (!passed)
             ^ "  failed " ^ Int.toString (!failed)
             ^ "  errored " ^ Int.toString (!errored)
             ^ "  skipped " ^ Int.toString (!skipped) ^ "\n");
        { passed = !passed, failed = !failed, errored = !errored,
          skipped = !skipped } : tally
      end

  end
