#!/bin/sh
# Turn the logs tools/ci-run.sh recorded into one Markdown report.
#
#   usage: tools/ci-report.sh DIR [ID...]
#
# Writes to standard output.  With no IDs, reports on every ID that has a
# .status file in DIR, in the order given below.
#
# The report says what the suite said and nothing more.  It carries the run
# header from each log -- int precision, word size, Char.maxOrd, the real
# format -- because the same source produces different boundary values on a
# 32-bit and a 63-bit implementation, so a failure only means something
# alongside the widths it was measured at.
set -e
cd "$(dirname "$0")/.."

dir=$1
[ -n "$dir" ] || { echo "usage: $0 DIR [ID...]" >&2; exit 2; }
shift

ids=$*
if [ -z "$ids" ]; then
  ids=""
  for id in smlnj mlton polyml mlkit; do
    [ -f "$dir/$id.status" ] && ids="$ids $id"
  done
fi

label() {
  case $1 in
    smlnj)  echo "SML/NJ" ;;
    mlton)  echo "MLton" ;;
    polyml) echo "Poly/ML" ;;
    mlkit)  echo "MLKit" ;;
    *)      echo "$1" ;;
  esac
}

# The tally line the runner prints last: "passed N  failed N  errored N ...".
field() { awk -v want="$2" '$1 == "passed" { for (i = 1; i < NF; i += 2) if ($i == want) print $(i+1) }' "$1" | tail -1; }

# The run header: two spaces, a name, then the value.
header_rows() {
  sed -n '/^Standard ML Basis Library test suite$/,/^$/p' "$1" \
    | sed -n 's/^  \([A-Za-z][A-Za-z ]*[A-Za-z]\) \{2,\}\(.*\)$/| \1 | \2 |/p' \
    | grep -v '^| \(seed\|trials\) |'
}

# Everything between the failure banner and the tally, blank lines squeezed.
failure_block() {
  awk '/^--- failures/ { f = 1; next } /^passed / { f = 0 } f' "$1" | sed '/^$/d'
}

echo "# Standard ML Basis Library conformance"
echo
first=$(set -- $ids; echo "$1")
if [ -n "$first" ] && [ -s "$dir/$first.log" ]; then
  seed=$(sed -n 's/^  seed  *\(.*\)$/\1/p' "$dir/$first.log" | head -1)
  trials=$(sed -n 's/^  trials  *\([0-9][0-9]*\).*$/\1/p' "$dir/$first.log" | head -1)
  [ -n "$seed" ] && echo "Seed \`$seed\`, $trials trials per property."
  [ -n "$CI_HOST" ] && echo "Host \`$CI_HOST\`."
  echo
fi

echo "| Implementation | Version | Tests | Passed | Failed | Errored | Skipped |"
echo "| --- | --- | ---: | ---: | ---: | ---: | ---: |"
for id in $ids; do
  version=$(cat "$dir/$id.version" 2>/dev/null || echo "unknown")
  if [ "$(cat "$dir/$id.status")" = completed ]; then
    p=$(field "$dir/$id.log" passed)
    f=$(field "$dir/$id.log" failed)
    e=$(field "$dir/$id.log" errored)
    s=$(field "$dir/$id.log" skipped)
    total=$((p + f + e + s))
    echo "| $(label "$id") | $version | $total | $p | $f | $e | $s |"
  else
    echo "| $(label "$id") | $version | \`did not build\` | | | | |"
  fi
done
echo

echo "A failure is a defect in the implementation under test, not in this"
echo "suite, so a red column here is a finding rather than a broken build."
echo "\`did not build\` is the one outcome that stops nothing being learned:"
echo "the compiler rejected the source before any test could run."
echo

for id in $ids; do
  version=$(cat "$dir/$id.version" 2>/dev/null || echo "unknown")
  echo "## $(label "$id")"
  echo
  if [ "$(cat "$dir/$id.status")" != completed ]; then
    echo "\`$version\` could not build the suite. The last of what it printed:"
    echo
    echo '```'
    # Compilers that narrate every file they read would otherwise fill the
    # excerpt with progress lines and push the error itself out of view.
    grep -v '^\[' "$dir/$id.log" | tail -25
    echo '```'
    echo
    continue
  fi

  p=$(field "$dir/$id.log" passed)
  f=$(field "$dir/$id.log" failed)
  e=$(field "$dir/$id.log" errored)
  s=$(field "$dir/$id.log" skipped)

  echo "| | |"
  echo "| --- | --- |"
  echo "| Version | $version |"
  header_rows "$dir/$id.log"
  echo "| Result | **$p passed, $f failed, $e errored, $s skipped** |"
  echo

  if [ "$((f + e))" -eq 0 ]; then
    echo "Nothing failed."
    echo
  else
    echo "<details><summary>$((f + e)) failing tests</summary>"
    echo
    echo '```'
    failure_block "$dir/$id.log"
    echo '```'
    echo
    echo "</details>"
    echo
  fi
done
