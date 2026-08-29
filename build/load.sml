(* Sequential loader for systems without a build manager (Poly/ML, Moscow ML).
 * Run from the repository root:
 *
 *   poly --script build/load.sml
 *   poly --script build/load.sml -- --trials 50 --only List
 *
 * The order below is the dependency order; the CM and MLB files derive theirs
 * from the same list in build/sources.txt.
 *)
use "src/framework/random.sml";
use "src/framework/gen.sml";
use "src/framework/show.sml";
use "src/framework/assert.sml";
use "src/framework/test.sml";
use "src/framework/runner.sml";
use "src/config/config.sml";
use "src/config/selected.sml";
use "src/tests/test-general.sml";
use "src/tests/test-option.sml";
use "src/tests/test-bool.sml";
use "src/tests/test-list.sml";
use "src/tests/test-list-pair.sml";
use "src/tests/test-int.sml";
use "src/tests/test-word.sml";
use "src/tests/test-char.sml";
use "src/tests/test-string.sml";
use "src/tests/test-substring.sml";
use "src/tests/test-string-cvt.sml";
use "src/tests/test-vector.sml";
use "src/tests/test-array.sml";
use "src/tests/test-slice.sml";
use "src/tests/test-real.sml";
use "src/tests/test-math.sml";
use "src/tests/test-time.sml";
use "src/tests/test-os-path.sml";
use "src/tests/test-byte.sml";
use "src/tests/test-os-process.sml";
use "src/tests/test-text-io.sml";
use "src/tests/all-tests.sml";
use "src/main.sml";

(* Poly/ML passes its own command line through CommandLine.arguments, script
 * name and all, so only what follows a -- separator is meant for the suite. *)
val () =
  let
    fun afterSeparator [] = []
      | afterSeparator ("--" :: rest) = rest
      | afterSeparator (_ :: rest) = afterSeparator rest
  in
    ignore (Main.runWith (afterSeparator (CommandLine.arguments ())))
  end;
