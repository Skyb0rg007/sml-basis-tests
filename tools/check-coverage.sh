#!/bin/sh
# Check that every Basis member listed in required-members.txt, and every
# member of the signatures the optional structures introduce listed in
# optional-members.txt, is exercised somewhere in the test sources.
#
# This is a coverage *floor*, not a proof: it shows that nothing was
# overlooked, not that every test of every member is a thorough one.
#
# Two kinds of indirection have to be resolved before grepping.  Test files
# abbreviate structure names (SS for Substring, W8V for Word8Vector, ...), and
# the generic tests in gen-*.sml are written against a signature and applied to
# several instances, so `W.andb` there stands for Word.andb, Word8.andb and
# LargeWord.andb at once.  Both are expanded below.
set -e
cd "$(dirname "$0")/.."

plain=$(find src/tests src/framework -name '*.sml' ! -name 'gen-*.sml')
optional_plain=$(find src/optional -name '*.sml' ! -name 'gen-*.sml')

# Abbreviations, longest first so the substitutions do not interfere.
expand_abbrevs() {
  sed -e 's/\bCVS\./CharVectorSlice./g'   -e 's/\bCAS\./CharArraySlice./g' \
      -e 's/\bCV\./CharVector./g'         -e 's/\bCA\./CharArray./g' \
      -e 's/\bW8VS\./Word8VectorSlice./g' -e 's/\bW8AS\./Word8ArraySlice./g' \
      -e 's/\bW8V\./Word8Vector./g'       -e 's/\bW8A\./Word8Array./g' \
      -e 's/\bW8\./Word8./g' \
      -e 's/\bVS\./VectorSlice./g'        -e 's/\bAS\./ArraySlice./g' \
      -e 's/\bSS\./Substring./g'          -e 's/\bSIO\./TextIO.StreamIO./g' \
      -e 's/\bFS\./OS.FileSys./g'         -e 's/\bPath\./OS.Path./g' \
      -e 's/\bLI\./LargeInt./g'           -e 's/\bLW\./LargeWord./g' \
      -e 's/\bLR\./LargeReal./g'          -e 's/\bII\./IntInf./g' \
      -e 's/\bA2\./Array2./g'
}

# The optional structures each generic optional file is applied to, read out
# of the per-implementation profiles rather than repeated here, so that adding
# a structure to a profile brings it into the coverage check too.  The union
# across profiles is the right set: the question a coverage floor asks is
# whether the suite exercises a member anywhere, not whether every
# implementation reaches it.
instances_of() {
  grep -h "structure $1 = " src/optional/opt-*.sml \
    | sed "s/.*structure $1 = //; s/[^A-Za-z0-9_].*//" | sort -u
}

# One copy of each generic file per instance it is applied to in
# test-instances.sml.
generic_corpus() {
  for s in CharVector Word8Vector CharArray Word8Array; do
    sed "s/\bSeq\./$s./g" src/tests/gen-mono-seq.sml
  done
  for s in CharVectorSlice Word8VectorSlice CharArraySlice Word8ArraySlice; do
    sed "s/\bSlice\./$s./g" src/tests/gen-mono-slice.sml
  done
  for s in Word Word8 LargeWord; do
    sed "s/\bW\./$s./g" src/tests/gen-numeric.sml
  done
  for s in Int LargeInt Position; do
    sed "s/\bI\./$s./g" src/tests/gen-numeric.sml
  done
  for s in Real LargeReal; do
    sed "s/\bR\./$s./g" src/tests/gen-numeric.sml
  done
  for s in $(instances_of Pack); do
    sed "s/\bPack\./$s./g" src/optional/gen-pack-word.sml
  done
  for s in $(instances_of Big); do
    sed "s/\bBig\./$s./g" src/optional/gen-pack-real.sml
  done
  for s in $(instances_of Little); do
    sed "s/\bLittle\./$s./g" src/optional/gen-pack-real.sml
  done
}

corpus=$( { cat $plain $optional_plain; generic_corpus; } | expand_abbrevs )

missing=0
checked=0
unexercised=0

check_list() {
while IFS= read -r entry; do
  case "$entry" in ''|'#'*) continue ;; esac
  case "$entry" in
    *"|"*)
      # Annotated as not callable from inside a running test: reported
      # separately so it is accounted for rather than silently skipped.
      echo "NOT CALLABLE IN-PROCESS  ${entry%%|*}  (${entry#*|})"
      unexercised=$((unexercised + 1))
      continue
      ;;
  esac
  checked=$((checked + 1))
  bare=${entry##*.}
  struct=${entry%.*}
  if printf '%s' "$corpus" | grep -qF "$entry"; then
    continue
  fi
  case "$struct" in
    # Members of these structures are also in the top-level environment and
    # are normally written unqualified, or are infix operators.
    List|General|Option|Bool)
      if printf '%s' "$corpus" | grep -qE "(^|[^A-Za-z0-9_.'])$bare([^A-Za-z0-9_']|$)"; then
        continue
      fi
      ;;
  esac
  echo "MISSING  $entry"
  missing=$((missing + 1))
done < "$1"
}

check_list tools/required-members.txt
required_checked=$checked
required_unexercised=$unexercised

checked=0
unexercised=0
check_list tools/optional-members.txt

echo
echo "checked $required_checked required members and $checked members of the"
echo "optional structures' own signatures, $missing not mentioned in the test sources"
echo "$required_unexercised further members cannot be called from inside a running test"
[ "$missing" -eq 0 ]
