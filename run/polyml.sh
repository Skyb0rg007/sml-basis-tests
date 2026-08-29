#!/bin/sh
# Run under Poly/ML.  Extra arguments are passed to the suite after the
# separator Poly/ML requires.
set -e
cd "$(dirname "$0")/.."
if [ $# -eq 0 ]; then
  exec poly --script build/load.sml
else
  exec poly --script build/load.sml -- "$@"
fi
