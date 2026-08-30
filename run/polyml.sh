#!/bin/sh
# Run under Poly/ML.  Extra arguments are passed to the suite after the
# separator Poly/ML requires.
#
# The default loader includes the optional structures Poly/ML provides.  Pass
# --core as the first argument to load the portable one instead, which names
# no optional structure at all.
set -e
cd "$(dirname "$0")/.."
load=build/load-polyml.sml
if [ "$1" = "--core" ]; then load=build/load.sml; shift; fi
if [ $# -eq 0 ]; then
  exec poly --script "$load"
else
  exec poly --script "$load" -- "$@"
fi
