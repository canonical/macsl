# macsl WS mechanisms — design stubs (M-3 … M-7)

**Status: DESIGN ONLY.** Nothing in this file is implemented. Each section is a TODO with a planned
`\context` keyword, the predicate/obligation, the red control, and the TCB impact — so the design is
on record and honest about what is *not* built. The shipped mechanisms (H-T, H-I1, H-R, H-E, H-S, H-I2,
H-D, and WS1 stage-1 `\guarded_by`/`\stable_check`) are documented in `usage.md` and `happy-roadmap.md`;
this file covers only the remaining, **unbuilt** ones.

For each mechanism the **TCB impact** column states what enters the trusted computing base. Per **Issue
6**, any mechanism that grows the WP-discharged cost/ranking set (M-5, M-6) must land its new lemma as
an **admit-free `*_hardened.v`** under `axiom-wp/coqwp/` **plus a Lean twin** (the dual-TP leg), or be
recorded as a classified entry in `axiom-wp/coqwp/AUDIT.md`. A cost/ranking lemma that is merely
`Admitted` (or asserted as a WP `lemma`-as-axiom) is **not** done.

---

## M-3 — Principal identity (Spoofing, beyond the H-S discipline)

- **Planned `\context`:** `\context(\authenticated_as(P))` (or `\speaks_for`).
- **Predicate / obligation:** an **uninterpreted** `\principal(P)` marker plus an injected precondition,
  at each guarded op, that the *current* principal equals the named one — i.e. the op runs **as** an
  identified principal, not merely after *some* check succeeded (which is all H-S/`\precond` proves).
  The identity proof itself stays a trusted declaration-only contract (`whoami()`-style), exactly like
  `verify_token`; `\principal` carries **no behavioural axiom**.
- **Red control:** `auth_confused_deputy` — an op reachable on a path where principal A's credential
  authorizes an action attributed to principal B (a privilege-confused/forwarding bug). The injected
  `\principal(B)` obligation is unprovable → red. Green twin: the op carries the matching principal.
- **TCB impact:** the identity oracle stays Specified/Assumed (GH1); no Coq lemma; no `axiom-wp` growth.

## M-4 — Tamper-evident log (Repudiation, beyond append-only)

- **Planned `\context`:** `\context(\tamper_evident)` (sugar over `\postcond` + a chained-hash ghost).
- **Predicate / obligation:** a **checked postcondition** that each appended record commits the running
  hash of its predecessor — `log_mac[n] == H(log_mac[n-1], rec[n])` over a ghost MAC chain — so any
  in-place edit of an earlier record breaks the chain. `H` is an **uninterpreted** logic function (the
  collision-resistance assumption is the trusted boundary, **not** an axiom macsl smuggles); macsl
  proves only the *chaining discipline* (every append extends the chain; nothing rewrites a committed
  link).
- **Red control:** `rewrite_then_keep_mac` — overwrites `log[k]` for `k < n` but leaves `log_mac`
  unchanged; the chain-consistency postcondition at the next append goes red. Green twin: append-only +
  recompute the chain forward.
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

| Mechanism | New `\context` | Grows `axiom-wp` hardened set (Issue 6)? |
|---|---|---|
| M-3 principal identity | `\authenticated_as` | no |
| M-4 tamper-evident log | `\tamper_evident` | no |
| M-5 cost/timing NI | `\noninterference(\cost)` | **yes** (step-bound lemma) |
| M-6 fuel/cost/resource | `\fuel` / `\cost` / `\resource` | **yes** (ranking lemma) |
| M-7 lattice flow | `\flows_to` | only if the order is a proved lemma (not a cost lemma) |

None of the above is implemented. When one lands it must add: the parse-dispatch arm + keyword, its
red/green control pair under `tests/`, a `usage.md` section, the non-vacuity gate wiring, and (M-5/M-6)
the admit-free hardened lemma + Lean twin per Issue 6.
