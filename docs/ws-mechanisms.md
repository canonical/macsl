# macsl WS mechanisms — M-3 … M-7

**Status: M-3, M-4 (Phase B / WS3, WS4) and M-5, M-6, M-7 (Phase C / WS5, WS6, WS7) are IMPLEMENTED**
(M-5 ships the cost channel + `\declassify`; **stateful store-duplication NI is an honest documented
PARTIAL** — see M-5 below). Each section records the shipped `\context` keyword, the predicate/obligation,
the red control + its without/with verdicts, and the TCB impact. The shipped mechanisms (H-T, H-I1, H-R,
H-E, H-S, H-I2, H-D, WS1 stage-1 `\guarded_by`/`\stable_check`, WS3 `\authorized`, WS4 `\tamper_evident`,
and now WS5 `\noninterference(\cost)`/`\declassify`, WS6 `\fuel`, WS7 `\flow`) are documented in
`usage.md` and `happy-roadmap.md`.

For each mechanism the **TCB impact** column states what enters the trusted computing base. Per **Issue
6**, any mechanism that grows the WP-discharged cost/ranking set (M-5, M-6) must land its new lemma as
an **admit-free `*_hardened.v`** under `axiom-wp/coqwp/` **plus a Lean twin** (the dual-TP leg), or be
recorded as a classified entry in `axiom-wp/coqwp/AUDIT.md`. A cost/ranking lemma that is merely
`Admitted` (or asserted as a WP `lemma`-as-axiom) is **not** done.

---

## M-3 — Principal identity (Spoofing, beyond the H-S discipline) — **IMPLEMENTED (WS3)**

- **`\context`:** `\context(\authorized)`. (The design floated `\authenticated_as(P)`/`\speaks_for`; the
  shipped keyword is `\authorized`, reading a `principal`/operation association in the policy body.)
- **Predicate / obligation:** an **uninterpreted** `\authorized(principal, op)` predicate, injected at
  **each protected write site** (reusing the H-T walk, exactly like `\guarded_by`), with the policy body
  conventionally `authorized(current_principal, OP)`. The obligation states the op runs **as** an
  identified, genuinely-authorized principal — not merely after *some* check succeeded (all H-S/`\precond`
  proves). The identity proof itself stays a trusted declaration-only contract (`authenticate()`/
  `whoami()`-style, `ensures authorized(current_principal, OP)`); `\authorized` carries **no behavioural
  axiom**.
- **Red control (shipped):** `forged_principal` (`tests/phase8/principal_neg.c`) — the protected op runs
  against a **forged/literal** principal claimed by fiat, skipping the trusted `authenticate()` binding.
  The injected `authorized(current_principal, OP_WRITE)` obligation is unprovable → **red** (without:
  `Proved goals 2/3`; strip `-macsl` → `No goal generated`, i.e. the obligation is load-bearing). Green
  twin `protected_op` (`principal_pos.c`): the op runs after `authenticate()` → `3/3` green.
- **TCB impact:** the identity oracle stays Specified/Assumed (GH1); no Coq lemma; no `axiom-wp` growth.

## M-4 — Tamper-evident log (Repudiation, beyond append-only) — **IMPLEMENTED (WS4)**

- **`\context`:** `\context(\tamper_evident)` (sugar over `\postcond` + a chained-hash obligation).
- **Predicate / obligation:** a **checked postcondition** that each committed record commits the running
  hash of its predecessor — `logbuf[i].mac == \hash(logbuf[i-1].mac, logbuf[i].rec)` for `0 < i < len`
  — so any in-place edit of an earlier record breaks the chain. `\hash` (= H) is the **single
  uninterpreted** logic function: macsl declares/uses it with **no behavioural axiom** (the
  collision-resistance assumption is the trusted crypto boundary, **not** an axiom macsl smuggles).
  macsl's `\hash` marker resolves to a same-named user logic function (`hash`) so the policy and the
  trusted MAC primitive's contract (`ensures \result == hash(prev, rec)`) share one H. macsl proves
  only the *chaining discipline* (every append extends the chain; nothing rewrites a committed link).
- **Red control (shipped):** `splice_log` (`tests/phase8/hashchain_neg.c`) — overwrites an
  already-committed `logbuf[k].rec` (k < len-1) but leaves the macs stale; the chain postcondition goes
  **red** (`Proved goals 3/4`; strip `-macsl` → `3/3`, obligation load-bearing). Green twin
  `append_record` (`hashchain_pos.c`): append-only + recompute the chain forward via `compute_mac` →
  `8/8` green.
- **TCB impact:** `H`'s cryptographic strength is Specified/Assumed (GH1). No new WP cost lemma → **no
  `axiom-wp` growth.** (This is H-R hardening, not a quantitative mechanism.)

## M-5 — Cost / timing noninterference (Information disclosure, timing channel) — **IMPLEMENTED (WS5), with an honest PARTIAL**

- **`\context`:** `\context(\noninterference(\cost))` — the **relational timing variant** of the `\fuel`
  spine. Tail: `\secret(param, ...)` (the secret split, as H-I2) and an optional `\declassify(value,
  ...)` (audited release points).
- **Predicate / obligation (IMPLEMENTED):** macsl extends the H-I2 self-composition twin
  (`emit_selfcomp_cost`, reusing `emit_selfcomp`'s public/secret formal split) with a **ghost step
  counter** (`__macsl_cost`, the same `fuel_visitor` cost model). The synthesized twin `f__costcomp`
  runs `f` twice (public shared, secret split a/b), **resets/snapshots** the counter around each call
  into `ca`/`cb`, and asserts `ca == cb` — equal public inputs ⇒ equal step count. The cost **value**
  is carried by the target's cost contract (`ensures __macsl_cost == …`, the fixture's, in terms of
  public state), exactly the WS4 split where `\hash`'s value is the trusted contract's; the counter is
  a **ground ghost variable** (no ranking lemma, no axiom). Bound: **modelled steps, not wall-clock /
  cache / µarch** (GH3 remains).
- **`\declassify` (IMPLEMENTED):** `\declassify(v, ...)` names **audited release points** — a deliberate
  release on record (a feedback audit note, never silent). Honest scope: in the cost channel the
  obligation is over the **aggregate** step count, so `\declassify` is the *audit record* of an intended
  release; a *per-value structural exemption* is the value-channel form (future).
- **Red control (shipped):** `timing_oracle` (`tests/phase11/cost_neg.c`) — constant **result** (no
  value leak; plain `\noninterference` passes) but a secret-dependent **branch/step count** (early-return
  compare): `ca == cb` is unprovable → **red** (`Proved goals 2/3`; strip `-macsl` → `No goal generated`,
  i.e. the cost twin is entirely macsl-generated, the obligation is load-bearing). Green twin
  `cost_pos.c`: constant-work (secret-independent cost) → `3/3` green.
- **PARTIAL — stateful (store-duplication) NI (honest):** the **store-duplication** form of NI (renaming
  the heap into two disjoint copies and relating them) is **not** implemented this pass. The shipped
  mechanism is the **cost channel** (a counter over modelled steps) + `\declassify` increments, reasoning
  **modularly** through the target's contract — sound, but it does **not** discharge a relational property
  that depends on duplicated *mutable store* state. This is left as a documented partial (do not read the
  cost-channel green as full stateful NI).
- **TCB impact (Issue 6):** the cost observable is a **ground ghost counter** and the relation is a plain
  equality over it — **no ranking/step-bound lemma is introduced**, so **this mechanism does NOT grow the
  hardened set.** (The earlier design floated a step-bound lemma; the ground-counter encoding avoids it,
  which is the preferred Issue-6 outcome.)

## M-6 — Fuel / cost / resource (Denial of service, quantitative) — **IMPLEMENTED (WS6)**

- **`\context`:** `\context(\fuel)` (the canonical spine). The bound is the policy property,
  conventionally `\fuel <= N`, where **`\fuel` is a per-site meta-term** resolving to the injected ghost
  counter.
- **Predicate / obligation (IMPLEMENTED):** macsl injects a **function-local ghost step counter**
  (`__macsl_fuel`, `mk_fuel_counter`/`fuel_visitor`), `++`'d at each **loop back-edge** and **call site**,
  and emits the bound `\fuel <= N` as a **checked postcondition**. On each instrumented loop it
  **auto-frames** the counter (adds `__macsl_fuel` to the loop's `assigns` and a `0 <= __macsl_fuel`
  invariant) so the user's existing loop annotations stay valid and the redness is genuinely about the
  bound. This is the quantitative iteration bound the shipped `\total` deliberately omits ("does at most
  N steps", not merely "terminates").
- **Red control (shipped):** `algorithmic_dos` (`tests/phase9/fuel_neg.c`) — a terminating-but-input-
  superlinear path (`n*n` call steps) under a **linear** bound `\fuel <= 100`: the counter is not bounded
  by the budget → **red** (`Proved goals 18/19`; strip `-macsl` → `11/11`, i.e. the bound is the only
  red, fully macsl-supplied — the refutation probe). Green twin `bounded_work` (`fuel_pos.c`): 3
  straight-line call steps under `\fuel <= 4` → `3/3` green.
- **Scope note (honest):** the per-site counter is a **ground** mechanism. A `\fuel` bound on a **loop**
  is provable green only when the loop carries an invariant tying iterations to the counter; because
  `__macsl_fuel` is macsl-injected (not nameable in a hand-written loop invariant this pass), the green
  positive is demonstrated on **straight-line/bounded** work, and the loop case is the **honest red**
  (an unbounded loop cannot meet a linear budget). `\cost(ranking)` (a supplied ranking) and
  `\resource(budget)` (alloc/recursion/handle pools) are the two **projections** named in `usage.md`;
  the shipped `\fuel` is their common spine.
- **TCB impact (Issue 6):** `\fuel` stays a **ground per-site counter** — the bound is an ordinary
  inequality over a real ghost variable, **no new logic symbol, no ranking lemma, no axiom**. **This
  mechanism does NOT grow the `axiom-wp` hardened set** (the preferred Issue-6 outcome, stated
  explicitly).

## M-7 — Lattice flow (Information disclosure, multi-level) — **IMPLEMENTED (WS7)**

- **`\context`:** `\context(\flow)` over a **user-declared** security lattice. The policy property is the
  flow predicate, conventionally a no-flow-up / ownership statement over the user's partial order `\leq`
  and labelling `\label(...)`.
- **Predicate / obligation (IMPLEMENTED):** `\flow` walks the target's **write sites** (the H-T walk,
  like `\authorized`) and injects, at each one, the policy's flow predicate — e.g.
  `\leq(\label(&source), \label(\lhost_written))` (you may write a target only with data whose label the
  target's label dominates: no high-to-low / no cross-owner flow). `\leq` resolves to the user's `leq`
  and `\label` to the user's `label` (the same-named-symbol discipline as `\hash`). This **folds vertical
  EoP** (no write-up) **and horizontal RBAC** (no cross-owner write) into **one** property over the
  lattice — where this cleanly subsumes the FE2-style per-pair horizontal-RBAC workaround
  (`tests/small_example/rbac_horizontal.c`), one lattice obligation replaces the bespoke check.
- **`\leq` / `\label` stay UNINTERPRETED:** macsl declares them profile-less and emits **zero axioms**
  about them. The lattice **order axioms** (reflexivity / antisymmetry / transitivity) are the **user's
  own structural `axiomatic` block** — definitional, satisfied by any partial order (like H-E's integer
  encoding) — not a behavioural fact macsl smuggles. The **label values** come from a trusted boundary
  contract (a `reclassify()`-style `ensures leq(...)`), exactly as `authenticate()` establishes
  `authorized` in WS3.
- **Red control (shipped):** `cross_tenant` (`tests/phase10/flow_neg.c`) — a write that crosses an
  ownership boundary (flows up) with no `reclassify` on the path: the flow predicate is unprovable →
  **red** (`Proved goals 2/3`; strip `-macsl` → `No goal generated`, the obligation is load-bearing).
  Green twin `legit_write` (`flow_pos.c`): the write routed through the trusted `reclassify` gate → `3/3`
  green.
- **TCB impact:** the lattice order is the **user's** structural `axiomatic` (definitional, auditable),
  **not** a macsl cost lemma — **no `axiom-wp` growth.** The relabel/declassify gate is
  Specified/Assumed (GH1).

---

## Summary: which mechanisms touch the hardened TCB

| Mechanism | New `\context` | Status | Grows `axiom-wp` hardened set (Issue 6)? |
|---|---|---|---|
| M-3 principal identity | `\authorized` | **implemented (WS3)** | no |
| M-4 tamper-evident log | `\tamper_evident` | **implemented (WS4)** | no |
| M-5 cost/timing NI | `\noninterference(\cost)` + `\declassify` | **implemented (WS5)**; stateful NI PARTIAL | **no** (ground ghost counter, not a step-bound lemma) |
| M-6 fuel/cost/resource | `\fuel` | **implemented (WS6)** | **no** (ground per-site counter, not a ranking lemma) |
| M-7 lattice flow | `\flow` | **implemented (WS7)** | no (order is the user's structural axiomatic) |

All five mechanisms are implemented (parse-dispatch arm + keyword, red/green control pair under
`tests/phase8/` (M-3/M-4), `tests/phase9/` (M-6 `\fuel`), `tests/phase10/` (M-7 `\flow`), `tests/phase11/`
(M-5 cost NI), `usage.md` sections, non-vacuity + refutation gate wiring). **No mechanism grew the
hardened set**: M-5 and M-6 use **ground ghost counters** (the bound/relation is an ordinary
(in)equality over a real ghost variable), avoiding the step-bound/ranking lemma the earlier design
floated — the preferred Issue-6 outcome. M-7's lattice order is the **user's** structural `axiomatic`,
not a macsl cost lemma. The only honest residual is **M-5 stateful (store-duplication) NI** (see M-5).
