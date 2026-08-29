#!/bin/sh
# Build and run under SML/NJ.  Extra arguments are passed to the suite.
set -e
cd "$(dirname "$0")/.."
ml-build build/sources.cm Main.main basis-tests >/dev/null
heap=$(ls basis-tests.*-* 2>/dev/null | head -1)
if [ -z "$heap" ]; then echo "no heap image produced" >&2; exit 1; fi
exec sml "@SMLload=$heap" "$@"
