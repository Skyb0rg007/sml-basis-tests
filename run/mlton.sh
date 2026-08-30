#!/bin/sh
# Build and run under MLton.  Extra arguments are passed to the suite.
#
# The default build description includes the optional structures MLton
# provides -- IntInf, the sized integers, words and reals, PackWord, PackReal,
# Array2 and the int and real sequences.  Pass --core as the first argument to
# build the portable description instead, which names no optional structure at
# all and so compiles on any implementation.
set -e
cd "$(dirname "$0")/.."
mlb=build/sources-mlton.mlb
if [ "$1" = "--core" ]; then mlb=build/sources.mlb; shift; fi
mlton -output basis-tests-mlton "$mlb"
exec ./basis-tests-mlton "$@"
