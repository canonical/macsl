#!/usr/bin/env bash
# dualtp gate (../../docs/frama-c-dual-tp-spec.md §5.4b, §5.7) — the syntactic Coq<->Lean leg.
# Fail-closed: missing python3 -> nonzero (INFRA-MISSING); any corpus miss or
# lemma cross-check mismatch -> nonzero.
set -u
cd "$(dirname "$0")"
command -v python3 >/dev/null 2>&1 || { echo "INFRA-MISSING: python3 not on PATH"; exit 2; }
rc=0
echo "== canonicalizer adversarial corpus (§5.7) =="
python3 test_canonical.py || rc=1
echo "== leg-2 Coq<->Lean cross-check (§5.4b) =="
python3 crosscheck.py || rc=1
[ "$rc" -eq 0 ] && echo "DUALTP OK" || echo "DUALTP FAILURES"
exit $rc
