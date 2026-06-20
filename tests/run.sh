#!/usr/bin/env bash
# macsl Phase-0 test runner.
#
# Self-contained: builds the plugin, then runs each fixture with autoload
# DISABLED (so an installed MetAcsl does not clash on the shared \prop/\written
# builtins) and only WP + macsl loaded.  Each case asserts on WP's verdict line
# or on a macsl diagnostic.  Exit code 0 iff every case passes.
#
# Usage:  ./tests/run.sh            (expects the framac-coq8 opam env active)
set -u

here="$(cd "$(dirname "$0")" && pwd)"
root="$(dirname "$here")"
cd "$root"

echo "== building =="
dune build 2>&1 | sed 's/^/  /' || { echo "BUILD FAILED"; exit 2; }

CMXS="$root/_build/default/src/macsl.cmxs"
[ -f "$CMXS" ] || { echo "plugin not built: $CMXS"; exit 2; }

BASE=(-no-autoload-plugins -load-module "$CMXS")
WP=(-load-plugin wp -wp -wp-prover alt-ergo,z3 -wp-timeout 5)

pass=0; fail=0
check () {  # name  expected-regex  command...
  local name="$1" pat="$2"; shift 2
  local out; out="$("$@" 2>&1)"
  if grep -qE "$pat" <<<"$out"; then
    echo "PASS  $name"; pass=$((pass+1))
  else
    echo "FAIL  $name  (expected /$pat/)"; echo "$out" | sed 's/^/      | /'
    fail=$((fail+1))
  fi
}

echo "== Phase-0 cases =="

# 1. Instrumentation is visible in place (the non-vacuity gate, part 1).
check "instr/print" 'assert macsl: iso: meta: .separated' \
  frama-c "${BASE[@]}" -macsl -print tests/phase0/writing_neg.c

# 2. Negative control: the secret-writing site does NOT prove (teeth).
check "neg/wp-catches" 'Proved goals: +4 / 5' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase0/writing_neg.c

# 3. Positive control: nothing writes secret -> everything proves.
check "pos/wp-allgreen" 'Proved goals: +4 / 4' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase0/writing_pos.c

# 4. Vacuity: a policy that matches no write site must WARN, not pass silently.
check "zero-expansion-warns" 'zero-expansion. Warning' \
  frama-c "${BASE[@]}" -macsl tests/phase0/zero_targets.c

# 5. list-targets reports the expansion count.
check "list-targets" 'policy iso .writing.: 3 assertion' \
  frama-c "${BASE[@]}" -macsl -macsl-list-targets tests/phase0/writing_neg.c

# 6. -macsl-set selects a subset (here: a name that does not exist -> 0 policies).
check "policy-select" 'Will process 0 policies' \
  frama-c "${BASE[@]}" -macsl -macsl-set nosuch tests/phase0/writing_neg.c

echo "== Phase-1 cases (H-I1 read confinement) =="

# 7. Reading instrumentation lands at read sites, not the write target.
check "read/print" 'noread: meta: .separated.&secret, &secret' \
  frama-c "${BASE[@]}" -macsl -print tests/phase1/reading_neg.c

# 8. Negative control: the secret-READING site does NOT prove.
check "read/neg-catches" 'Proved goals: +3 / 4' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase1/reading_neg.c

# 9. Positive control: nothing reads secret -> everything proves.
check "read/pos-allgreen" 'Proved goals: +4 / 4' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase1/reading_pos.c

echo "== Phase-2 cases (H-R audit-log completeness + immutability) =="

# 10. The completeness obligation is injected as a checked postcondition.
check "audit/print" 'check ensures audit: meta:' \
  frama-c "${BASE[@]}" -macsl -print tests/phase2/audit_pos.c

# 11. Completeness positive: sys_write logs its change -> provable.
check "audit/pos" 'Proved goals: +3 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase2/audit_pos.c

# 12. Completeness negative: sys_unlink changes disk without logging -> red.
check "audit/neg-catches" 'Proved goals: +2 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase2/audit_neg.c

# 13. Immutability positive: append touches only the new slot -> provable.
check "immut/pos" 'Proved goals: +3 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase2/immut_pos.c

# 14. Immutability negative: rewriting an old slot -> append-only red.
check "immut/neg-catches" 'Proved goals: +2 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase2/immut_neg.c

echo "== Phase-3 cases (H-E privilege monotonicity) =="

# 15. \diff(\ALL,{sudo_gate}) exempts the gate: 2 targets, not 3.
check "priv/gate-exempt" 'policy noesc .postcond.: 2 assertion' \
  frama-c "${BASE[@]}" -macsl -macsl-list-targets tests/phase3/priv_pos.c

# 16. Positive: non-gate functions never raise privilege -> all proved.
check "priv/pos" 'Proved goals: +8 / 8' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase3/priv_pos.c

# 17. Negative: a confused-deputy `escalate` raises priv -> monotonicity red.
check "priv/neg-catches" 'Proved goals: +4 / 5' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase3/priv_neg.c

echo "== Phase-4 cases (H-S check-before-use capabilities) =="

# 18. The capability is injected as a requires (precondition) on the guarded op.
check "authn/print" 'requires authn: meta: session_ok' \
  frama-c "${BASE[@]}" -macsl -print tests/phase4/authn_pos.c

# 19. Positive: authenticated caller (verify_token then sys_write) -> all proved.
check "authn/pos" 'Proved goals: +5 / 5' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase4/authn_pos.c

# 20. Negative: direct call without verify_token -> call-site precondition red.
check "authn/neg-catches" 'Proved goals: +4 / 5' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase4/authn_neg.c

echo "== Phase-5 cases (H-I2 noninterference via self-composition) =="

# 21. macsl synthesizes the self-composition twin driver.
check "ni/synthesized" 'void check__selfcomp.int attempt, int stored_a, int stored_b' \
  frama-c "${BASE[@]}" -macsl -print tests/phase5/noninterf_pos.c

# 22. Positive: result independent of the secret -> relational assert proved.
check "ni/pos" 'Proved goals: +3 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase5/noninterf_pos.c

# 23. Negative: result leaks the secret -> relational assert red.
check "ni/neg-catches" 'Proved goals: +2 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase5/noninterf_neg.c

echo "== Worked example (small_example/banking: H-R + H-S + H-T together) =="

# 24. Compliant banking core: all four policies hold.
check "banking/compliant" 'Proved goals: +18 / 18' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/small_example/banking.c

# 25. Four attacks, one per policy: exactly four goals red.
check "banking/attacks" 'Proved goals: +25 / 29' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/small_example/banking_attacks.c

echo "== $pass passed, $fail failed =="
[ "$fail" -eq 0 ]
