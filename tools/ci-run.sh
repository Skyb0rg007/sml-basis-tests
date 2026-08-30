#!/bin/sh
# Run the suite under one implementation and record what happened, without
# letting a failing run stop the caller.
#
#   usage: tools/ci-run.sh ID OUTDIR [suite options...]
#
# ID is one of smlnj, mlton, polyml, mlkit -- the name of the script in run/.
# Three files are written to OUTDIR:
#
#   ID.version   what the compiler calls itself
#   ID.rc        the exit status of the run
#   ID.log       everything the build and the run printed
#   ID.status    completed | incomplete
#
# "completed" means the run reached its tally line, whether or not tests
# failed.  The distinction matters: a conformance suite reporting defects in
# an implementation is doing its job, and is not the same event as the suite
# failing to build at all.  Only the second is a reason to stop.
set -e
cd "$(dirname "$0")/.."

id=$1
out=$2
[ -n "$id" ] && [ -n "$out" ] || { echo "usage: $0 ID OUTDIR [options...]" >&2; exit 2; }
shift 2

# Every version command is piped, so a compiler that reports its version with
# a non-zero exit status -- mlton prints it above a usage message and does --
# does not take the script down with it.
case "$id" in
  smlnj)  version="SML/NJ $(sml @SMLversion 2>&1 | head -1)" ;;
  mlton)  version=$(mlton 2>&1 | head -1) ;;
  polyml) version=$(poly -v 2>&1 | head -1) ;;
  mlkit)  version=$(mlkit --version 2>&1 | head -1) ;;
  *)      echo "unknown implementation: $id" >&2; exit 2 ;;
esac

mkdir -p "$out"
# Poly/ML pads its version line with runs of spaces; squeeze them so the
# string sits in a Markdown table cell without stretching it.
printf '%s\n' "$version" | tr -s ' ' > "$out/$id.version"

if "run/$id.sh" "$@" > "$out/$id.log" 2>&1; then rc=0; else rc=$?; fi
printf '%s\n' "$rc" > "$out/$id.rc"

if grep -q '^passed ' "$out/$id.log"
then echo completed > "$out/$id.status"
else echo incomplete > "$out/$id.status"
fi

printf '%s: %s (exit %s)\n' "$id" "$(cat "$out/$id.status")" "$rc"
