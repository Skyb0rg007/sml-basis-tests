(* main.sml -- command line entry point.
 *
 * Two kinds of input reach the suite.  Facts about the implementation come
 * from the TEST_CONFIG structure chosen at build time, because they decide
 * which tests are meaningful at all.  Facts about this particular run -- seed,
 * number of trials, which tests to run -- come from the command line, because
 * changing them should not mean rebuilding.
 *)

structure Main =
  struct
    structure Tests = AllTestsFn (Config)

    val usage =
      String.concatWith "\n"
        [ "usage: basis-tests [options]"
        , ""
        , "  --seed N       seed for the random generator (default "
          ^ Int.toString (#seed Runner.defaults) ^ ")"
        , "  --trials N     trials per property (default "
          ^ Int.toString (#trials Runner.defaults) ^ ")"
        , "  --max-size N   largest generated size (default "
          ^ Int.toString (#maxSize Runner.defaults) ^ ")"
        , "  --only PAT     run only tests whose full name contains PAT"
        , "  --verbose      list passing tests as well as failing ones"
        , "  --help         print this message"
        , ""
        ]

    exception BadUsage of string

    fun intArg (flag, s) =
      case Int.fromString s of
          SOME n => n
        | NONE => raise BadUsage (flag ^ " expects an integer, got " ^ s)

    fun parse (args, opts : Runner.options) =
      let
        val { seed, trials, maxSize, verbose, only } = opts
      in
        case args of
            [] => opts
          | "--verbose" :: rest =>
              parse (rest, { seed = seed, trials = trials, maxSize = maxSize,
                             verbose = true, only = only })
          | "--seed" :: v :: rest =>
              parse (rest, { seed = intArg ("--seed", v), trials = trials,
                             maxSize = maxSize, verbose = verbose, only = only })
          | "--trials" :: v :: rest =>
              parse (rest, { seed = seed, trials = intArg ("--trials", v),
                             maxSize = maxSize, verbose = verbose, only = only })
          | "--max-size" :: v :: rest =>
              parse (rest, { seed = seed, trials = trials,
                             maxSize = intArg ("--max-size", v),
                             verbose = verbose, only = only })
          | "--only" :: v :: rest =>
              parse (rest, { seed = seed, trials = trials, maxSize = maxSize,
                             verbose = verbose, only = SOME v })
          | flag :: [] =>
              if flag = "--seed" orelse flag = "--trials"
                 orelse flag = "--max-size" orelse flag = "--only"
              then raise BadUsage (flag ^ " expects an argument")
              else raise BadUsage ("unrecognised argument: " ^ flag)
          | flag :: _ => raise BadUsage ("unrecognised argument: " ^ flag)
      end

    fun header (opts : Runner.options) =
      String.concatWith "\n"
        [ "Standard ML Basis Library test suite"
        , "  configuration   " ^ Config.implName
        , "  int precision   "
          ^ (case Int.precision of
                 NONE => "arbitrary"
               | SOME p => Int.toString p ^ " bits")
        , "  word size       " ^ Int.toString Word.wordSize ^ " bits"
        , "  char maxOrd     " ^ Int.toString Char.maxOrd
        , "  real precision  " ^ Int.toString Real.precision
          ^ " digits, radix " ^ Int.toString Real.radix
        , "  seed            " ^ Int.toString (#seed opts)
        , "  trials          " ^ Int.toString (#trials opts) ^ " per property"
        , ""
        ]

    fun runWith args =
      if List.exists (fn a => a = "--help") args
      then (print usage; OS.Process.success)
      else
      let
        val opts = parse (args, Runner.defaults)
      in
          let
            val () = print (header opts ^ "\n")
            val { failed, errored, ... } = Runner.run opts Tests.suite
          in
            if failed = 0 andalso errored = 0
            then OS.Process.success
            else OS.Process.failure
          end
      end
      handle BadUsage msg =>
        (print (msg ^ "\n\n" ^ usage); OS.Process.failure)

    (* SML/NJ's ml-build calls this. *)
    fun main (_, args) = runWith args
  end
