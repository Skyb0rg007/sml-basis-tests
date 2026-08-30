#!/bin/sh
# Build and run under MLKit, which reads the same MLB file as MLton.
#
# This uses the portable description, which names no optional structure.
# MLKit does provide several of them, but no profile has been written and
# checked against it here; writing one means a file in build/optional/ and a
# matching src/optional/opt-mlkit.sml, as for the other three.
set -e
cd "$(dirname "$0")/.."
mlkit -o basis-tests-mlkit build/sources.mlb
exec ./basis-tests-mlkit "$@"
