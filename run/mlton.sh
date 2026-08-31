#!/bin/sh
# Build and run under MLton.  Extra arguments are passed to the suite.
#
# The default build description includes the optional structures MLton
# provides -- IntInf, the sized integers, words and reals, PackWord, PackReal,
# Array2 and the int and real sequences.  Pass --core as the first argument to
# build the portable description instead, which names no optional structure at
# all and so compiles on any implementation.
#
# -drop-pass bounceVars is not a tuning choice.  MLton 20241230 compiles the
# whole suite as one program, and its bounceVars pass -- an RSSA register
# pressure pass whose cost grows with the size of a single function -- needs
# more than 7GB on the function that builds the test tree, so the compiler is
# killed on an ordinary machine.  Dropping that one pass costs a little
# generated code quality and nothing else; every other pass runs as usual.
set -e
cd "$(dirname "$0")/.."
mlb=build/sources-mlton.mlb
if [ "$1" = "--core" ]; then mlb=build/sources.mlb; shift; fi
mlton -drop-pass bounceVars -output basis-tests-mlton "$mlb"
exec ./basis-tests-mlton "$@"
