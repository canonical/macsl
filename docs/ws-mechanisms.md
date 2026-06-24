# macsl WS mechanisms — M-3 … M-7

**Status: M-3 and M-4 are IMPLEMENTED (Phase B / WS3, WS4); M-5, M-6, M-7 are DESIGN ONLY.** Each
design-stub section is a TODO with a planned `\context` keyword, the predicate/obligation, the red
control, and the TCB impact — so the design is on record and honest about what is *not* built. The
shipped mechanisms (H-T, H-I1, H-R, H-E, H-S, H-I2, H-D, WS1 stage-1 `\guarded_by`/`\stable_check`, and
now WS3 `\authorized` / WS4 `\tamper_evident`) are documented in `usage.md` and `happy-roadmap.md`; the
M-3/M-4 sections below are kept as the **implemented**-record, and M-5/M-6/M-7 cover the remaining
**unbuilt** ones.

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

## M-5 — Cost / timing noninterference (Information disclosure, timing channel)

- **Planned `\context`:** `\context(\noninterference(\cost))` — the **relational timing variant** of the
  `\fuel` spine (see the Resource vocabulary in `usage.md` / `happy-roadmap.md`).
- **Predicate / obligation:** self-composition (as H-I2) instrumented with a **ghost step counter**;
  the relational obligation is `steps_a == steps_b` for equal public inputs and distinct secrets —
  i.e. the step count does not depend on the secret (a constant-time-style obligation over WP-modelled
  steps). Bound: this is **modelled steps, not wall-clock / cache / µarch** (GH3 remains).
- **Red control:** `branch_on_secret` — a function whose loop trip count or branch depends on the secret
  (e.g. early-return password compare); `steps_a == steps_b` is unprovable → red. Green twin: a
  fixed-trip-count (constant-work) compare.
- **TCB impact (Issue 6):** the step-counting model and any **ranking/step-bound lemma** the relational
  VC needs must ship as an **admit-free `axiom-wp/coqwp/*_hardened.v` + Lean twin**, or a classified
  `AUDIT.md` entry. **This mechanism GROWS the hardened set.**

## M-6 — Fuel / cost / resource (Denial of service, quantitative)

- **Planned `\context`:** `\context(\fuel(expr))` (canonical spine), with projections
  `\context(\cost(ranking))` and `\context(\resource(budget))` — vocabulary settled in Issue 4
  (`usage.md` → Resource vocabulary; `happy-roadmap.md` top note + §4).
- **Predicate / obligation:**
  - `\fuel(expr)` / `\cost(ranking)` — inject a ghost step counter incremented per loop body, with the
    declared bound `expr`/ranking carried as a loop invariant; the closing VC proves the counter never
    exceeds the bound (the quantitative iteration bound the shipped `\total` deliberately omits).
  - `\resource(budget)` — the same discipline over **allocations / recursion depth / handle counts**
    against an explicit declared budget ("don't exhaust the pool").
- **Red control:** `unbounded_retry` — a loop whose trip count exceeds the declared `\fuel`, or a
  recursion deeper than the `\resource` budget; the budget invariant goes red. Green twin: a loop with a
  matching, provable bound.
- **TCB impact (Issue 6):** any **ranking lemma** used to discharge the budget VC must ship as an
  **admit-free `*_hardened.v` + Lean twin** under `axiom-wp/coqwp/`, or a classified `AUDIT.md` entry.
  **This mechanism GROWS the hardened set.** A budget proved only via an `Admitted` ranking lemma is
  **not** done.

## M-7 — Lattice flow (Information disclosure, multi-level)

- **Planned `\context`:** `\context(\flows_to(L1, L2))` over a declared security lattice.
- **Predicate / obligation:** generalize H-I1 read-confinement from a single secret region to a
  **finite security lattice** (a small `axiomatic` order `leq(level, level)` or a Coq-proved order
  lemma). At each write whose target is labelled `Lhi`, inject `\separated(\read, region(Llo))` for
  every `Llo` not `leq` the target's label — i.e. no high-to-low flow. The lattice order is the only
  new logic; the per-site obligations reuse the `\reading`/`\writing` walk.
- **Red control:** `declassify_without_gate` — a write of a `High` value into a `Low`-labelled region
  with no declassifier on the path; the flow-separation obligation goes red. Green twin: the same flow
  routed through a trusted `\declassify` gate (itself a declaration-only boundary).
- **TCB impact:** if the lattice order ships as an `axiomatic` block it is a **definitional** assumption
  (acceptable, like H-E's integer encoding); if it ships as a **proved order lemma** it must be
  admit-free (no `axiom-wp` *cost* growth, but the order lemma is auditable). The `\declassify` gate is
  Specified/Assumed (GH1).

---

## Summary: which mechanisms touch the hardened TCB

| Mechanism | New `\context` | Status | Grows `axiom-wp` hardened set (Issue 6)? |
|---|---|---|---|
| M-3 principal identity | `\authorized` | **implemented (WS3)** | no |
| M-4 tamper-evident log | `\tamper_evident` | **implemented (WS4)** | no |
| M-5 cost/timing NI | `\noninterference(\cost)` | design stub | **yes** (step-bound lemma) |
| M-6 fuel/cost/resource | `\fuel` / `\cost` / `\resource` | design stub | **yes** (ranking lemma) |
| M-7 lattice flow | `\flows_to` | design stub | only if the order is a proved lemma (not a cost lemma) |

M-3 and M-4 are implemented (parse-dispatch arm + keyword, red/green control pair under
`tests/phase8/`, `usage.md` sections, non-vacuity gate wiring). M-5/M-6/M-7 remain design stubs; when one
lands it must add the same, plus (M-5/M-6) the admit-free hardened lemma + Lean twin per Issue 6.
