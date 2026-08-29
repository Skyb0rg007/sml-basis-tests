#!/bin/sh
# Build and run under MLton.  Extra arguments are passed to the suite.
set -e
cd "$(dirname "$0")/.."
mlton -output basis-tests-mlton build/sources.mlb
exec ./basis-tests-mlton "$@"
