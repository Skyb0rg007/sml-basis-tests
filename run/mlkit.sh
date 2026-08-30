#!/bin/sh
# Build and run under MLKit, which reads an MLB file as MLton does.
#
# The default description adds src/compat/compat-mlkit.sml, which supplies
# String.scan: MLKit 4.7.22 does not have it, and a whole-program compiler
# stops at the first unbound identifier, so without it none of the suite runs.
# The tests of String.scan are skipped on this build rather than passed --
# they would be testing this suite's own code.
#
# Pass --core as the first argument to build the portable description instead,
# which supplies nothing and so does not compile here; that is the finding.
set -e
cd "$(dirname "$0")/.."
mlb=build/sources-mlkit.mlb
if [ "$1" = "--core" ]; then mlb=build/sources.mlb; shift; fi
mlkit -o basis-tests-mlkit "$mlb"
exec ./basis-tests-mlkit "$@"
