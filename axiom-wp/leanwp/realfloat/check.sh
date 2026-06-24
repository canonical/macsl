#!/usr/bin/env bash
# Verify the mathlib-dependent leanwp twins (bijection + reals/floats).
# Same discipline as ../check.sh: no sorry, compiles, #print axioms ⊆ standard set.
# FAIL-CLOSED: missing lake/mathlib -> non-zero (INFRA-MISSING).
set -u
cd "$(dirname "$0")"
source "$HOME/.elan/env" 2>/dev/null || true
ALLOWED='propext|Classical.choice|Quot.sound'
command -v lake >/dev/null 2>&1 || { echo "INFRA-MISSING: lake not on PATH"; exit 2; }
# Fetch prebuilt mathlib oleans, then VERIFY they actually landed: `lake exe cache get`
# can exit 0 yet leave Mathlib.olean absent (silent partial/transient download), which
# otherwise surfaces downstream as a confusing "COMPILE FAILED". Retry, then fail-closed
# as INFRA-MISSING (not a twin failure) if the cache still didn't populate.
MOLEAN=".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
get_cache() { echo "== lake exe cache get =="; lake exe cache get || return 1; [ -f "$MOLEAN" ]; }
if ! get_cache; then
  echo "  cache incomplete; retrying once..."; sleep 5
  get_cache || true
fi
# The mathlib Azure cache can lack a handful of oleans for a *tagged* commit — including
# the top-level `Mathlib.olean` aggregate that Cfloat.lean's `import Mathlib` needs (the
# v4.31.0 tag fabf563 is missing ~26, surfacing as "some files were not found in the
# cache"). `lake exe cache get` is best-effort, so FILL the gap by BUILDING the missing
# oleans from the (already-cached) dependency closure — bounded to the few the cache
# lacked, NOT a from-scratch mathlib build. Fail-closed as INFRA-MISSING only if even the
# build cannot produce the aggregate (a genuine toolchain/cache infra failure, not a twin
# failure).
if [ ! -f "$MOLEAN" ]; then
  echo "== cache gap: building missing oleans (lake build Mathlib) =="
  lake build Mathlib || { echo "INFRA-MISSING: mathlib unavailable (cache gap + lake build Mathlib failed)"; exit 2; }
  [ -f "$MOLEAN" ] || { echo "INFRA-MISSING: $MOLEAN still absent after lake build"; exit 2; }
fi
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
