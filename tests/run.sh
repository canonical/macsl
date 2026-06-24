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

echo "== Phase-6 cases (H-D denial of service: totality + no-fault) =="
# (Cases 33-34; numbered after the worked example to keep its cross-references 24-32
#  intact. D is the dedicated phase fixture for the letter previously demonstrated
#  only inside the worked example, cases 28-29.)

# 33. H-D positive control: a parser whose loop always advances -> \total proves it
#     terminates (and -wp-rte: never faults). "Never hangs, never crashes."
check "hd/totality-pos" 'Proved goals: +9 / 9' \
  frama-c "${BASE[@]}" "${WP[@]}" -wp-rte -macsl tests/phase6/totality_pos.c

# 34. H-D negative control: the confused parser (advances only on odd i) -> the loop
#     variant cannot be shown to strictly decrease -> the \total termination goal
#     goes red. The teeth: "a malformed length field hangs the parser."
check "hd/totality-neg-catches" 'Proved goals: +8 / 9' \
  frama-c "${BASE[@]}" "${WP[@]}" -wp-rte -macsl tests/phase6/totality_neg.c

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

echo "== Phase-7 cases (WS1 stage 1: \\guarded_by lock-held + \\stable_check) =="
# These prove ONLY lock-held-at-access (resp. guard-stable-marker), NOT
# check-then-act atomicity. A green \guarded_by suite is NOT "races handled":
# the race-family crosswalk cell stays TRUSTED until WS1 stage-2. See
# docs/usage.md "Concurrency (WS1 stage 1)".
#
# `held` / `stable` are UNINTERPRETED logic predicates (the macsl \held/\stable
# markers). Each pair is provable WITH the lock/snapshot that establishes the
# obligation and red WITHOUT it.

# 35. \guarded_by instruments at the guarded write site (non-vacuity, part 1).
check "race/guarded-print" 'assert macsl: session_guard: meta: held' \
  frama-c "${BASE[@]}" -macsl -print tests/phase7/race_session_pos.c

# 36-38. \guarded_by POSITIVE controls: the lock is acquired before the write,
#        so the injected held(lock) holds -> all green.
check "race/session-pos" 'Proved goals: +3 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase7/race_session_pos.c
check "race/audit-pos" 'Proved goals: +3 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase7/race_audit_pos.c
check "race/priv-pos" 'Proved goals: +3 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase7/race_priv_pos.c

# 39-41. \guarded_by NEGATIVE controls: the shared write happens WITHOUT the
#        lock -> held(lock) is unprovable at the site -> red (the teeth).
check "race/session-neg-catches" 'Proved goals: +2 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase7/race_session_neg.c
check "race/audit-neg-catches" 'Proved goals: +2 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase7/race_audit_neg.c
check "race/priv-neg-catches" 'Proved goals: +2 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase7/race_priv_neg.c

# 42. The obligation is LOAD-BEARING: strip the policy (no -macsl) and the SAME
#     negative fixture proves vacuously -> the red comes from macsl, not the C.
check "race/neg-vacuous-without-obligation" 'No goal generated|Proved goals: +2 / 2' \
  frama-c "${BASE[@]}" "${WP[@]}" tests/phase7/race_session_neg.c

# 43-45. \stable_check: the marker that an interleaving argument is OWED.
check "stable/print" 'assert macsl: guard_stable: meta: stable' \
  frama-c "${BASE[@]}" -macsl -print tests/phase7/stable_check_pos.c
check "stable/pos" 'Proved goals: +3 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase7/stable_check_pos.c
check "stable/neg-catches" 'Proved goals: +2 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase7/stable_check_neg.c

# 46. Non-vacuity gate: -macsl-warn-key zero-expansion=abort must NOT trip on a
#     guarded control (it really expanded over a site).
check "race/non-vacuity-zero-abort" 'assert macsl: priv_guard' \
  frama-c "${BASE[@]}" -macsl -macsl-warn-key zero-expansion=abort -print \
    tests/phase7/race_priv_pos.c

echo "== Phase-8 cases (WS3 \\authorized principal identity + WS4 \\tamper_evident) =="
# WS3 (M-3): \authorized binds a protected op to a PRINCIPAL IDENTITY, not a
# boolean. The injected obligation is authorized(current_principal, OP) over an
# UNINTERPRETED `authorized` predicate. Where H-S proved "you called the
# checker", M-3 proves the principal is GENUINE: a forged/literal principal does
# NOT satisfy `authorized` without the trusted authenticate() binding. The token
# check itself stays a trusted declaration-only contract (GH1).

# 47. \authorized instruments at the protected write site (non-vacuity, part 1).
check "authz/principal-print" 'assert macsl: principal_bound: meta: authorized' \
  frama-c "${BASE[@]}" -macsl -print tests/phase8/principal_pos.c

# 48. POSITIVE control: caller runs authenticate() -> the principal is genuinely
#     bound -> authorized(current_principal, OP_WRITE) holds -> all green.
check "authz/principal-pos" 'Proved goals: +3 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase8/principal_pos.c

# 49. NEGATIVE control (forged_principal): the op runs against a FORGED principal
#     with no authenticate() -> authorized(..) unprovable at the site -> red.
check "authz/forged-neg-catches" 'Proved goals: +2 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase8/principal_neg.c

# 50. The obligation is LOAD-BEARING: strip the policy (no -macsl) and the SAME
#     forged fixture proves vacuously -> the red comes from macsl, not the C.
check "authz/neg-vacuous-without-obligation" 'No goal generated|Proved goals: +2 / 2' \
  frama-c "${BASE[@]}" "${WP[@]}" tests/phase8/principal_neg.c

# 51. Non-vacuity gate: zero-expansion=abort must NOT trip on the positive (it
#     really expanded over a protected-op site).
check "authz/non-vacuity-zero-abort" 'assert macsl: principal_bound' \
  frama-c "${BASE[@]}" -macsl -macsl-warn-key zero-expansion=abort -print \
    tests/phase8/principal_pos.c

# WS4 (M-4): \tamper_evident strengthens the repudiation obligation from a
# length predicate to a HASH CHAIN: logbuf[i].mac == \hash(logbuf[i-1].mac,
# logbuf[i].rec). `\hash` (= H) is the SINGLE uninterpreted logic function; macsl
# proves the CHAINING DISCIPLINE only. Collision-resistance of H is the crypto
# residual (GH1), NOT proved and NOT a smuggled axiom.

# 52. \tamper_evident emits the chain as a checked postcondition (the injected
#     obligation prints as `check ensures hashchain: meta:` — the label wraps to
#     the next line, so match it there).
check "tamper/chain-print" 'hashchain: meta:' \
  frama-c "${BASE[@]}" -macsl -print tests/phase8/hashchain_pos.c

# 53. POSITIVE control: append_record links the new slot via compute_mac
#     (\result == hash(prev,rec)) -> the chain is extended -> all green.
check "tamper/chain-pos" 'Proved goals: +8 / 8' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase8/hashchain_pos.c

# 54. NEGATIVE control (splice_log): rewriting an already-committed record
#     without recomputing the chain -> chain postcondition unprovable -> red.
check "tamper/splice-neg-catches" 'Proved goals: +3 / 4' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase8/hashchain_neg.c

# 55. The chain obligation is LOAD-BEARING: strip the policy and the SAME splice
#     fixture proves vacuously -> the red comes from macsl, not the C.
check "tamper/neg-vacuous-without-obligation" 'No goal generated|Proved goals: +3 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" tests/phase8/hashchain_neg.c

echo "== Phase-9 cases (WS6 / M-6: \\fuel bounded work) =="
# \fuel injects a ghost STEP COUNTER (__macsl_fuel) into the body, ++'d at each
# loop back-edge / call site, and emits the bound `\fuel <= N` as a CHECKED
# postcondition. `\fuel` is a per-site META-TERM resolving to the ground ghost
# counter -> NO new logic symbol, NO ranking lemma, NO axiom (no TCB growth).
# See docs/usage.md "Bounded work (WS6)".

# 56. \fuel emits the step-bound as a checked postcondition over the ghost counter
#     (non-vacuity, part 1).
check "fuel/bound-print" 'check ensures fuelbound: meta: __macsl_fuel' \
  frama-c "${BASE[@]}" -macsl -print tests/phase9/fuel_pos.c

# 57. POSITIVE control (bounded_work): straight-line work of 3 call steps under a
#     bound of 4 -> __macsl_fuel == 3 <= 4 -> green.
check "fuel/pos" 'Proved goals: +3 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase9/fuel_pos.c

# 58. NEGATIVE control (algorithmic_dos): input-superlinear work (n*n call steps)
#     under a LINEAR bound -> __macsl_fuel unbounded -> \fuel<=100 RED.
check "fuel/neg-catches" 'Proved goals: +18 / 19' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase9/fuel_neg.c

# 59. The bound is LOAD-BEARING: strip the policy (no -macsl) and the SAME fixture
#     proves vacuously (no fuel goal) -> the red comes from macsl, not the C.
check "fuel/neg-vacuous-without-obligation" 'No goal generated|Proved goals: +11 / 11' \
  frama-c "${BASE[@]}" "${WP[@]}" tests/phase9/fuel_neg.c

# 60. Non-vacuity gate: zero-expansion=abort must NOT trip on the positive (it
#     really instrumented a target function).
check "fuel/non-vacuity-zero-abort" 'check ensures fuelbound' \
  frama-c "${BASE[@]}" -macsl -macsl-warn-key zero-expansion=abort -print \
    tests/phase9/fuel_pos.c

echo "== Phase-10 cases (WS7 / M-7: \\flow lattice-parametric flow) =="
# \flow walks the target's write sites and injects a no-flow-up / ownership
# predicate over the USER's partial order `leq` and labelling `label(...)`.
# `\leq` / `\label` are UNINTERPRETED (macsl emits no order axioms); the lattice
# ORDER axioms (refl/antisym/trans) are the user's OWN structural axiomatic
# (definitional). Folds vertical EoP + horizontal RBAC into one property.
# See docs/usage.md "Lattice flow (WS7)".

# 61. \flow instruments at the flow-checked write site (non-vacuity, part 1).
check "flow/noflowup-print" 'noflowup: meta: leq' \
  frama-c "${BASE[@]}" -macsl -print tests/phase10/flow_pos.c

# 62. POSITIVE control (legit_write): the write target's label dominates the
#     caller-data label (established by the trusted reclassify gate) -> the
#     no-flow-up obligation `leq(label(&caller_data), label(&tenantA))` -> green.
check "flow/pos" 'Proved goals: +3 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase10/flow_pos.c

# 63. NEGATIVE control (cross_tenant): a write that crosses an ownership boundary
#     with no reclassify on the path -> the flow predicate is unprovable -> RED.
check "flow/neg-catches" 'Proved goals: +2 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase10/flow_neg.c

# 64. The flow obligation is LOAD-BEARING: strip the policy and the SAME fixture
#     proves vacuously (no flow goal) -> the red comes from macsl, not the C.
check "flow/neg-vacuous-without-obligation" 'No goal generated|Proved goals: +2 / 2' \
  frama-c "${BASE[@]}" "${WP[@]}" tests/phase10/flow_neg.c

echo "== Phase-11 cases (WS5 / M-5: \\noninterference(\\cost) + \\declassify) =="
# \noninterference(\cost) extends the H-I2 self-composition twin with a ghost
# STEP COUNTER (the cost channel __macsl_cost) and asserts the count is
# SECRET-INDEPENDENT across the two runs (`ca == cb`). The cost VALUE is the
# fixture's cost contract; the counter is a ground ghost variable -> NO ranking
# lemma, NO axiom (no TCB growth). \declassify(v) is an audited release point.
# Stateful (store-duplication) NI is an honest documented PARTIAL (see
# docs/ws-mechanisms.md M-5). See docs/usage.md "Cost-channel NI (WS5)".

# 65. macsl synthesizes the cost twin asserting equal step counts (`ca == cb`).
check "cost/twin-synthesized" 'assert macsl: ct_cost: meta: ca .* cb' \
  frama-c "${BASE[@]}" -macsl -print tests/phase11/cost_pos.c

# 66. POSITIVE control: constant-work compare (cost independent of the secret)
#     -> `ca == cb` discharges -> green.
check "cost/pos" 'Proved goals: +3 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase11/cost_pos.c

# 67. NEGATIVE control (timing_oracle): constant RESULT but secret-dependent
#     BRANCH/STEP count (early-return compare) -> `ca == cb` unprovable -> RED.
check "cost/neg-catches" 'Proved goals: +2 / 3' \
  frama-c "${BASE[@]}" "${WP[@]}" -macsl tests/phase11/cost_neg.c

# 68. The cost twin is LOAD-BEARING: strip the policy and the cost twin is not
#     generated at all -> the red comes entirely from macsl.
check "cost/neg-vacuous-without-obligation" 'No goal generated|Proved goals: +2 / 2' \
  frama-c "${BASE[@]}" "${WP[@]}" tests/phase11/cost_neg.c

# 69. \declassify records an audited release point (never silent): the audit note
#     is emitted, and the constant-work twin still discharges.
check "cost/declassify-audit" 'declassifies .attempt. .audited release point.' \
  frama-c "${BASE[@]}" -macsl tests/phase11/cost_declassify.c

echo "== $pass passed, $fail failed =="
[ "$fail" -eq 0 ]
