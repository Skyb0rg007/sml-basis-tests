#!/bin/sh
# Check that every required Basis member listed in required-members.txt is
# mentioned somewhere in the test sources.
#
# This is a coverage *floor*, not a proof: it shows that nothing was
# overlooked, not that every test is a good one.  Members reached only through
# an abbreviated structure name (A for Assert, CV for CharVector, and so on)
# are resolved by expanding the abbreviations the test files declare.
set -e
cd "$(dirname "$0")/.."

list=tools/required-members.txt
sources=$(find src/tests src/framework -name '*.sml')

# Structure abbreviations used inside the test files, longest first so that
# the substitutions do not interfere.
corpus=$(cat $sources | sed \
  -e 's/\bCVS\./CharVectorSlice./g'   -e 's/\bCAS\./CharArraySlice./g' \
  -e 's/\bCV\./CharVector./g'         -e 's/\bCA\./CharArray./g' \
  -e 's/\bW8VS\./Word8VectorSlice./g' -e 's/\bW8AS\./Word8ArraySlice./g' \
  -e 's/\bW8V\./Word8Vector./g'       -e 's/\bW8A\./Word8Array./g' \
  -e 's/\bW8\./Word8./g' \
  -e 's/\bVS\./VectorSlice./g'        -e 's/\bAS\./ArraySlice./g' \
  -e 's/\bSS\./Substring./g'          -e 's/\bSIO\./TextIO.StreamIO./g' \
  -e 's/\bFS\./OS.FileSys./g'         -e 's/\bPath\./OS.Path./g' \
  -e 's/\bLI\./LargeInt./g'           -e 's/\bLW\./LargeWord./g' \
  -e 's/\bLR\./LargeReal./g')

missing=0
checked=0
unexercised=0
while IFS= read -r entry; do
  case "$entry" in ''|'#'*) continue ;; esac
  case "$entry" in
    *"|"*)
      # Annotated as not callable from inside a running test; reported
      # separately so it is accounted for rather than silently skipped.
      name=${entry%%|*}
      why=${entry#*|}
      echo "NOT CALLABLE IN-PROCESS  ${name}  (${why})"
      unexercised=$((unexercised + 1))
      continue
      ;;
  esac
  checked=$((checked + 1))
  # Match the qualified name, or the bare member for the pervasive structures
  # whose members are also top-level (List, General, Option, Bool).
  bare=${entry#*.}
  struct=${entry%%.*}
  if printf '%s' "$corpus" | grep -qF "$entry"; then
    continue
  fi
  case "$struct" in
    List|General|Option|Bool)
      if printf '%s' "$corpus" | grep -qE "(^|[^A-Za-z0-9_.'])$bare([^A-Za-z0-9_']|$)"; then
        continue
      fi
      ;;
  esac
  echo "MISSING  $entry"
  missing=$((missing + 1))
done < "$list"

echo
echo "checked $checked required members, $missing not mentioned in the test sources"
echo "$unexercised further members cannot be called from inside a running test"
[ "$missing" -eq 0 ]
