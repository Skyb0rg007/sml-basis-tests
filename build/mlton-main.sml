(* Whole-program compilers run top-level code, so the entry point is an
 * effect rather than a named function.  Only the MLB build includes this. *)
val () = OS.Process.exit (Main.runWith (CommandLine.arguments ()))
