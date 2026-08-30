(* compat.sml -- what a build had to supply itself.
 *
 * An implementation may be missing a member the Basis requires.  That is a
 * finding, but on a whole-program compiler it is a fatal one: the suite does
 * not fail the test, it fails to compile, and the thousands of tests that
 * have nothing to do with the missing member never run either.
 *
 * A build may therefore supply the member itself, from src/compat/, so that
 * the rest of the suite can run.  What it must not do is then report a pass
 * for it.  Every substituted member is named here, and the tests that
 * exercise it are skipped with that as the reason, because a conformance
 * suite that tests its own code and calls the result conformance is worse
 * than one that does not run at all.  The run header lists them too, so the
 * substitution is visible to someone reading only the summary.
 *
 * This is the default: nothing substituted.  A build that needs a shim
 * replaces it through the @compat marker in build/sources.txt.
 *)

structure Compat =
  struct
    val substituted : string list = []
    fun isSubstituted name = List.exists (fn n => n = name) substituted
  end
