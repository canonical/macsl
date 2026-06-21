#!/usr/bin/env bash
# Verify the mathlib-dependent leanwp twins (bijection + reals/floats).
# Same discipline as ../check.sh: no sorry, compiles, #print axioms ⊆ standard set.
# FAIL-CLOSED: missing lake/mathlib -> non-zero (INFRA-MISSING).
set -u
cd "$(dirname "$0")"
source "$HOME/.elan/env" 2>/dev/null || true
ALLOWED='propext|Classical.choice|Quot.sound'
command -v lake >/dev/null 2>&1 || { echo "INFRA-MISSING: lake not on PATH"; exit 2; }
# fetch prebuilt mathlib oleans (no-op if already present)
lake exe cache get >/dev/null 2>&1 || { echo "INFRA-MISSING: mathlib cache unavailable"; exit 2; }
rc=0
for f in RealFloat.lean Cfloat.lean; do
  echo "== $f =="
  out="$(lake env lean "$f" 2>&1)" || { echo "  COMPILE FAILED"; echo "$out" | head; rc=1; continue; }
  printed="$(grep -E 'depends on axioms|does not depend' <<<"$out")"
  [ -z "$printed" ] && { echo "  FAIL: no #print axioms output"; rc=1; continue; }
  names="$(grep -oE '\[[^]]*\]' <<<"$printed" | tr -d '[]' | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -vE '^$')"
  bad=0
  for n in $names; do grep -qE "^(${ALLOWED})$" <<<"$n" || { echo "  FAIL: non-standard axiom: $n"; bad=1; }; done
  [ "$bad" -ne 0 ] && { rc=1; continue; }
  echo "  OK"
done
[ "$rc" -eq 0 ] && echo "ALL OK" || echo "FAILURES"
exit $rc
