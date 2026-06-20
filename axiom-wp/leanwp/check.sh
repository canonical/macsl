#!/usr/bin/env bash
# Verify the leanwp dual-TP twins (the Lean side of axiom-wp). For each .lean:
#   - no `sorry`,
#   - compiles under `lean`,
#   - every `#print axioms` line is a subset of the standard Lean kernel axioms
#     {propext, Classical.choice, Quot.sound}.
# FAIL-CLOSED: if the Lean toolchain is absent, exit non-zero (INFRA-MISSING) —
# a missing prover must NEVER read as PASS (see ../../frama-c-dual-tp-spec.md §5.6).
# Usage: source "$HOME/.elan/env" first (or have `lean` on PATH), then ./check.sh
set -u
cd "$(dirname "$0")"
source "$HOME/.elan/env" 2>/dev/null || true
ALLOWED='propext|Classical.choice|Quot.sound'
rc=0

if ! command -v lean >/dev/null 2>&1; then
  echo "INFRA-MISSING: lean not on PATH (run: source \$HOME/.elan/env)"; exit 2
fi
echo "lean: $(lean --version | head -1)"

shopt -s nullglob
for f in *.lean; do
  echo "== $f =="
  # 1. compile (also emits the file's `#print axioms` lines on stdout). A `sorry`
  #    compiles with a warning but surfaces as `sorryAx` in #print axioms, which
  #    the allow-list below rejects — so no separate (comment-fooled) text grep.
  out="$(lean "$f" 2>&1)" || { echo "  COMPILE FAILED"; echo "$out" | head; rc=1; continue; }
  # 2. axiom audit — require at least one #print axioms line, all axioms allow-listed
  printed="$(grep -E 'depends on axioms|does not depend on any axioms' <<<"$out")"
  if [ -z "$printed" ]; then
    echo "  FAIL: no '#print axioms' output — add it for each certified theorem"; rc=1; continue
  fi
  names="$(grep -oE '\[[^]]*\]' <<<"$printed" | tr -d '[]' | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -vE '^$')"
  bad=0
  for n in $names; do
    grep -qE "^(${ALLOWED})$" <<<"$n" || { echo "  FAIL: non-standard axiom: $n"; bad=1; }
  done
  [ "$bad" -ne 0 ] && { rc=1; continue; }
  echo "  OK"
  echo "$printed" | sed 's/^/    /'
done

[ "$rc" -eq 0 ] && echo "ALL OK" || echo "FAILURES"
exit $rc
