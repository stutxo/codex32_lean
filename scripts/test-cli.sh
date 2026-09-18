#!/usr/bin/env bash
# CLI integration-test harness; public, disposable fixtures only.
# Does not require Python or an external RNG.
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ -d .toolchain/bin ]]; then
  export PATH="$PWD/.toolchain/bin:$PATH"
fi
lake build codex32_test_cli
lake env lean --run Codex32Test/Cli/Tests.lean
cli="$PWD/.lake/build/bin/codex32_test_cli"
umask 077
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
checks=0

assert_equal() {
  if [[ "$1" != "$2" ]]; then
    printf 'CLI check failed: %s\n' "$3" >&2
    exit 1
  fi
  checks=$((checks + 1))
}

reject() {
  local input=$1
  shift
  if "$cli" "$@" < "$input" > "$scratch/stdout" 2> "$scratch/stderr"; then
    printf 'CLI accepted invalid input/arguments: %s\n' "$*" >&2
    exit 1
  fi
  [[ ! -s "$scratch/stdout" && -s "$scratch/stderr" ]] || {
    printf 'CLI failed to reject atomically: %s\n' "$*" >&2
    exit 1
  }
  checks=$((checks + 1))
}

seed=ffeeddccbbaa99887766554433221100
official=ms13cashsllhdmn9m42vcsamx24zrxgs3qqjzqud4m0d6nln
printf '%s\n' "$seed" > "$scratch/seed"
printf '%s\n' "$official" > "$scratch/secret"
assert_equal "$("$cli" encode cash 3 < "$scratch/seed")" "$official" 'official encoding'
assert_equal "$("$cli" decode < "$scratch/secret")" "$seed" 'official decoding'
printf '%s\r\n' "$seed" > "$scratch/crlf"
assert_equal "$("$cli" encode cash 3 < "$scratch/crlf")" "$official" 'seed CRLF'
printf '%s\n' ms13casha320zyxwvutsrqpnmlkjhgfedca2a8d0zehn8a0t \
  ms13cashcacdefghjklmnpqrstuvwxyz023949xq35my48dr \
  ms13cashd0wsedstcdcts64cd7wvy4m90lm28w4ffupqs7rm > "$scratch/official-shares"
assert_equal "$("$cli" recover < "$scratch/official-shares")" "$seed" 'official recovery'
awk '{printf "%s\r\n", $0}' "$scratch/official-shares" > "$scratch/crlf"
assert_equal "$("$cli" recover < "$scratch/crlf")" "$seed" 'share CRLF'
assert_equal "$("$cli" encode test 0 2 <<< 318c6318c6318c6318c6318c6318c631)" \
  ms10testsxxxxxxxxxxxxxxxxxxxxxxxxxx4nzvca9cmczlw 'official nonzero padding'

for length in 16 20 24 28 32 64; do
  hex=$(printf '%0*d' "$((length * 2))" 0)
  printf '%s\n' "$hex" > "$scratch/seed"
  "$cli" encode test < "$scratch/seed" > "$scratch/secret"
  assert_equal "$("$cli" decode < "$scratch/secret")" "$hex" "seed size $length"
  "$cli" split test 2 3 < "$scratch/seed" > "$scratch/shares"
  head -n 2 "$scratch/shares" > "$scratch/selected"
  assert_equal "$("$cli" recover < "$scratch/selected")" "$hex" "split seed size $length"
done

# Exercise the OS entropy path and long checksums for each threshold. For k+1
# output shares, recover EVERY distinct subset of size k, in reversed order.
longseed=$seed$seed$seed$seed
printf '%s\n' "$longseed" > "$scratch/seed"
for threshold in 2 3 4 5 6 7 8 9; do
  count=$((threshold + 1))
  "$cli" split cash "$threshold" "$count" < "$scratch/seed" > "$scratch/shares"
  assert_equal "$(wc -l < "$scratch/shares" | tr -d ' ')" "$count" 'output share count'
  for ((omit = 1; omit <= count; omit++)); do
    awk -v omit="$omit" 'NR != omit {line[++n]=$0} END {for(i=n;i>0;i--) print line[i]}' \
      "$scratch/shares" > "$scratch/selected"
    assert_equal "$("$cli" recover < "$scratch/selected")" "$longseed" \
      "long seed threshold $threshold subset omitting $omit"
  done
done

# All 31 non-secret indices are usable, including original random-share indices.
"$cli" split cash 9 31 < "$scratch/seed" > "$scratch/shares"
assert_equal "$(wc -l < "$scratch/shares" | tr -d ' ')" 31 'maximum share count'
awk 'NR % 3 == 0 && NR <= 27' "$scratch/shares" > "$scratch/selected"
assert_equal "$("$cli" recover < "$scratch/selected")" "$longseed" 'spread-out indices'

"$cli" --help > "$scratch/help"
[[ -s "$scratch/help" ]]
reject /dev/null
reject /dev/null unknown
reject /dev/null decode extra
reject /dev/null encode cash 1
reject /dev/null encode cash 10
reject /dev/null encode cash 3 32
reject /dev/null encode invalid
reject /dev/null encode 'ca!h'
reject /dev/null split cash 0 2
reject /dev/null split cash 3 2
reject /dev/null split cash 3 32
reject /dev/null split cash 3 1000000
reject /dev/null split cash -3 5
reject /dev/null split cash 3x 5
reject /dev/null recover
printf '%s\n' 0 > "$scratch/bad"
reject "$scratch/bad" encode test
printf '%s\n' zzeeddccbbaa99887766554433221100 > "$scratch/bad"
reject "$scratch/bad" split cash 3 5
printf '%s \n' "$seed" > "$scratch/bad"
reject "$scratch/bad" encode test
printf '%s\n%s\n' "$seed" "$seed" > "$scratch/bad"
reject "$scratch/bad" encode test
printf '%s\n' ms13cashsllhdmn9m42vcsamx24zrxgs3qqjzqud4m0d6nlq > "$scratch/bad"
reject "$scratch/bad" decode
head -n 1 "$scratch/shares" > "$scratch/bad"
reject "$scratch/bad" decode
reject "$scratch/bad" recover
head -n 8 "$scratch/shares" > "$scratch/bad"
head -n 1 "$scratch/shares" >> "$scratch/bad"
reject "$scratch/bad" recover
head -n 10 "$scratch/shares" > "$scratch/bad"
reject "$scratch/bad" recover
printf '%s\n\n' "$official" > "$scratch/bad"
reject "$scratch/bad" decode
awk 'NR == 3 {printf "%s\r\r\n", $0; next} {print}' "$scratch/official-shares" > "$scratch/bad"
reject "$scratch/bad" recover
awk 'NR == 3 {printf "%s\r", $0; next} {print}' "$scratch/official-shares" > "$scratch/bad"
reject "$scratch/bad" recover
printf '%s\n' "$official" > "$scratch/bad"
head -n 2 "$scratch/official-shares" >> "$scratch/bad"
reject "$scratch/bad" recover
printf '\377\376' > "$scratch/bad"
reject "$scratch/bad" decode
dd if=/dev/zero of="$scratch/oversized" bs=1048576 count=1 2>/dev/null
reject "$scratch/oversized" encode test
reject "$scratch/oversized" split cash 3 5
reject "$scratch/oversized" decode
reject "$scratch/oversized" recover
printf 'CLI integration checks passed: %s\n' "$checks"
