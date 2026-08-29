#!/bin/sh
# Build and run under MLKit, which reads the same MLB file as MLton.
set -e
cd "$(dirname "$0")/.."
mlkit -o basis-tests-mlkit build/sources.mlb
exec ./basis-tests-mlkit "$@"
