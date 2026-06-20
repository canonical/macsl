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

echo "== Worked example (small_example: all seven HAPPY families together) =="

# 24. Compliant banking core: seven policies across six families (H-R x2, H-S, H-T,
#     H-I1 read confinement, H-I2 noninterference, H-D availability/totality) all hold.
check "banking/compliant" 'Proved goals: +63 / 63' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/small_example/compliant.c

# 25. Eleven attacks, one per policy: exactly eleven goals red (attack 9 = FE2
#     horizontal-RBAC cross-account debit; attack 10 = FE10 silent audit
#     saturation; attack 11 = FE11 token-lifecycle replay, token_live on
#     replay_endpoint calling protected_op without a liveness check).
check "banking/attacks" 'Proved goals: +70 / 81' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/small_example/attacks.c

# 26. The policies proved on main.c's REAL transfer(), through the ACSL libc
#     (strcmp/strlen contracts) -- "outside WP's reach" was wrong. The 52 cover the
#     transfer body + nonrepud_complete (H-R) + priv_monotonic (H-E) through libc.
#     The full-AuditRecord nonrepud_append_only goal is scoped out here because on
#     this big function it is *context-bloated* (its loop + libc contracts inflate
#     every goal); the SAME frame is proved DETERMINISTICALLY in case 27 below, and
#     the scalar form is proved in case 24 -- so it is discharged, not skipped.
check "mainc/policy-on-real-transfer" 'Proved goals: +53 / 53' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl -wp-prop="-nonrepud_append_only" -wp-fct transfer tests/small_example/main.c

# 27. The append-only STRUCT frame, proved DETERMINISTICALLY -- under a bounded,
#     machine-independent step budget (not a wall-clock timeout). main.c's real
#     transfer cannot give a clean VC for this (context bloat, not difficulty); the
#     fact is isolated onto a tiny driver carrying log_transfer's exact frame
#     contract, and the two char[50] frames discharge under 50k steps. This is the
#     rigorous proof of nonrepud_append_only for the struct case. See
#     small_example/audit_append_frame.c.
check "audit-frame/deterministic" 'Proved goals: +6 / 6' \
  frama-c "${BASE[@]}" -load-plugin wp -wp -wp-prover alt-ergo,z3 -wp-split -wp-steps 50000 \
    -wp-timeout 60 -macsl tests/small_example/audit_append_frame.c

# 28. H-D availability, FULL claim on the bounded request handler: terminates
#     (\total -> a terminates clause WP discharges from the loop variant) AND
#     -wp-rte (never faults). The "never hangs, never crashes" theorem.
check "hd/availability-rte" 'Proved goals: +23 / 23' \
  frama-c "${BASE[@]}" "${WP[@]}" -wp-rte -macsl -wp-fct find_first_overdrawn \
    tests/small_example/compliant.c

# 29. H-D on a strtok parse loop — the get_query_param gap, isolated and FIXED.
#     Frama-C's shipped strtok contract omits a strict-progress `ensures`, so a
#     strtok loop has no provable variant. Adding the two SOUND ensures (advance-
#     when-room; non-NULL-token-implies-room) lets \total prove termination (and
#     -wp-rte the no-fault half). See small_example/strtok_terminates.c.
check "hd/strtok-terminates" 'Proved goals: +17 / 17' \
  frama-c "${BASE[@]}" "${WP[@]}" -wp-rte -macsl tests/small_example/strtok_terminates.c

# 30. FE2 horizontal access control, isolated and PROVED. Closes the EBIOS
#     crosswalk's FE2 gap: a role-2 (User) caller may debit ONLY their own
#     account. On main.c's string-keyed transfer the postcondition context-bloats
#     (caller-lookup loop + libc strcmp), like nonrepud_append_only; proved here on
#     the clean integer model. The matching cross-account attack is red in case 25.
check "rbac/horizontal-own-account" 'Proved goals: +13 / 13' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/small_example/rbac_horizontal.c

# 31. FE10 silent audit saturation, isolated and PROVED. Closes the headline
#     crosswalk residual: a transfer that cannot record itself must FAIL CLOSED, so
#     non-repudiation (balance changed => log grew) holds EVEN at capacity (precond
#     allows audit_len == NLOG). main.c carries the same fail-closed guard now; the
#     at-capacity proof lives here free of string context bloat. Red: case 25's
#     transfer_unlogged_atcap (moves money, records only if room).
check "audit/saturation-failclosed" 'Proved goals: +13 / 13' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/small_example/audit_saturation.c

# 32. FE11 token lifecycle (discipline half), isolated and PROVED. Closes the
#     check-before-use part of FE11: a protected op runs only against a CURRENTLY-
#     valid token (token_active == 1 at the gate), so a revoked/expired/replayed
#     token cannot authorize it. (Token unguessability + the expiry clock remain
#     the trusted boundary, spec §6.) Red: case 25's replay_endpoint.
check "token/lifecycle-live" 'Proved goals: +8 / 8' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/small_example/token_lifecycle.c

echo "== $pass passed, $fail failed =="
[ "$fail" -eq 0 ]
