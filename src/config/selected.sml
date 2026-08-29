(* selected.sml -- the one line a port has to change.
 *
 * Point this at ConfigUnix, ConfigWindows, ConfigMinimal, or at a structure
 * of your own matching TEST_CONFIG.  Nothing else in the suite names a
 * concrete configuration.
 *)

structure Config = ConfigUnix
