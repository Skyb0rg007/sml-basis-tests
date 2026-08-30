#!/bin/sh
# Build and run under SML/NJ.  Extra arguments are passed to the suite.
#
# The default build description includes the optional structures SML/NJ
# provides.  Pass --core as the first argument to build the portable
# description instead, which names no optional structure at all.
set -e
cd "$(dirname "$0")/.."
cm=build/sources-smlnj.cm
if [ "$1" = "--core" ]; then cm=build/sources.cm; shift; fi
ml-build "$cm" Main.main basis-tests >/dev/null
heap=$(ls basis-tests.*-* 2>/dev/null | head -1)
if [ -z "$heap" ]; then echo "no heap image produced" >&2; exit 1; fi
exec sml "@SMLload=$heap" "$@"
