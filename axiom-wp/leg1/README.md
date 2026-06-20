# Leg 1 (semantic Why3↔Coq) — `Memory.separated_trans` feasibility spike

Leg 1 of the dual-TP (`../../frama-c-dual-tp-spec.md` §4, §5.4a) anchors the Coq
realization lemma to **what Why3 means**, by proving — inside Coq, against the
Cohen–Johnson-Freyd denotational semantics —

> `separated_trans_Coq  ⟺  formula_rep … ⟦Why3(separated_trans)⟧`

This file records the **grounded feasibility spike** for the pilot lemma. The
obligation proof itself is **not yet started** — it is blocked on a heavy but
well-characterized build step (§3). Nothing here is a green; it is the honest
"start": ground truth + coverage check + build path.

## 1. Ground truth `Why3(L)` — extracted, and it matches both proofs
`why3-separated_trans.mlw` is the **verbatim** WP Why3 source
(`$(frama-c -print-share-path)/wp/why3/frama_c_wp/memaddr.mlw`, `lemma
separated_trans` @ line 107). By inspection the three statements are the **same
proposition** (variable renaming `lp,lq,lr ↔ a,b,c`):

| | `included` | `separated` | lemma |
|---|---|---|---|
| **Why3** (memaddr.mlw) | `lp>0 → (lq≥0 ∧ base p=base q ∧ off q≤off p ∧ off p+lp≤off q+lq)` | `lp≤0 ∨ lq≤0 ∨ base p≠base q ∨ off q+lq≤off p ∨ off p+lp≤off q` | `inc p lp q lq → sep q lq r lr → sep p lp r lr` |
| **Coq** (`../coqwp/Memory_hardened.v`) | identical | identical | identical |
| **Lean** (`../leanwp/Memory.lean`) | identical | identical | identical |

So the pilot's Coq+Lean twins are already faithful to the WP ground truth (an
eyeball confirmation today; leg 1 makes the Why3↔Coq half *mechanical*, leg 2 the
Coq↔Lean half). The `[ … ]` in the lemma is an **SMT trigger** — a prover hint,
semantically irrelevant; the denotation ignores it.

## 2. Fragment coverage (spec §5.8 gating check) — **PASS**
`Why3(separated_trans)` is first-order and lands inside the formalized fragment:
- **record type** `addr = { base:int; offset:int }` → a one-constructor ADT with
  field projections (the semantics supports ADTs + `match_rep`);
- **defined predicates** `included`/`separated` (definitional unfolding);
- **quantifiers** (`∀ p q r : addr, ∀ lp lq lr : int`), connectives
  (`→ ∨ ∧ ¬(=)`), and **`int`** arithmetic (`+ ≤ > =`);
- no higher-order, no exotic features; trigger ignored.

⇒ This lemma is **eligible** for leg-1 certification (no single-prover fallback
needed). Coverage must still be re-checked per lemma for the rest of Memory/Vset
and especially the `R`-based theories.

## 3. Build feasibility — FEASIBLE, heavy, and version-split (grounded)
The vendored notes (`/tmp …/docs/why3-semantics/`, mirrored from
`github.com/joscoh/why3-semantics`) are **three leaf files**; `formula_rep`
transitively needs the **full** project (`Syntax`, `Types`, `Interp`,
`FullInterp`, `Substitution`, `Typechecker`, …) — the `formula`/`term` inductive
itself lives in the un-vendored `Syntax.v`. Probed facts:
- the semantics targets **Rocq 9.x** (`Require Import Stdlib.…`, the post-8.21
  stdlib namespace) and the **Equations** plugin;
- `rocq-prover` **9.0.0–9.1.1** and **`coq-equations`** are installable in this
  opam universe; the upstream repo is reachable (pin a commit, e.g. current HEAD).

**Version split (the real wrinkle).** coqwp + WP's Coq driver require **Coq
8.20.1** (Rocq 9 breaks them — the reason for the `framac-coq8` switch). The
semantics requires **Rocq 9.x**. So leg 1 cannot live in the coqwp build; it is a
**separate Rocq-9 development** that *re-states* the addr/included/separated defs
+ the lemma (a trivial port — the `Memory_hardened.v` defs are plain `Z`/`lia`,
and `Stdlib.ZArith`+`Lia` exist on Rocq 9). The re-stated Coq lemma is the
`Coq(L)` that leg 1 anchors; the original `coqwp/Memory_hardened.v` (8.20.1) stays
the artifact WP's green actually rests on. Leg 2 then checks Coq(L) ≡ Lean(L).

## 4. The obligation, and a caveat
- Statement: `separated_trans_Coq ⟺ formula_rep γ pd pf vt vv ⟦sep_trans⟧ Hty`
  (or via `valid`/`satisfies` from `Logic.v`), with `included`/`separated`
  reflected as defined predicate symbols and `addr`/`int` interpreted per the
  theory.
- **`closed_satisfies_rep` does NOT apply here.** That collapse (validity →
  boolean `decide`) is for *closed integer VCs* (the SMT-escalated ACSL class).
  `separated_trans` is universally quantified over abstract `addr`/`int`, so prove
  the `⟺` against `formula_rep`-as-`Prop` by reasoning, not by evaluation
  (spec §5.4a, §10).

## 5. Next steps (the build recipe — explicit, not yet run)
1. `opam switch create dualtp-rocq9 --packages rocq-prover.9.1.1` (or matching);
   `opam install coq-equations` (+ any project deps).
2. Vendor the **full** `joscoh/why3-semantics` at a **pinned commit** under
   `axiom-wp/why3-semantics/` (mind the licence/attribution), and build it.
3. Read the real `Syntax.v` `formula`/`term` constructors; write the
   `⟦separated_trans⟧ : formula` term (the AST→`formula` bridge for this lemma).
4. Add the bridge **round-trip check** (pretty-print the `formula` back through
   Why3, diff vs `why3-separated_trans.mlw`) — spec §5.8, fail-closed.
5. Re-state the Memory defs under Rocq 9 and prove the §4 obligation; confirm it
   is axiom-clean (`Print Assumptions` ⊆ `A_coq`).
6. Wire a fail-closed `leg1/check.sh` + a CI job; flip `Memory.separated_trans`'s
   `crosscheck` status toward certified.

## Status
- [x] Ground-truth `Why3(L)` extracted; Why3≡Coq≡Lean confirmed by inspection.
- [x] Fragment coverage: **PASS** (in-fragment).
- [x] Build path grounded (Rocq 9 + Equations installable; full project reachable;
      version-split resolved as a separate Rocq-9 dev).
- [ ] Full semantics vendored + built. **(blocked-by-effort; recipe in §5)**
- [ ] `⟦separated_trans⟧` `formula` term + bridge round-trip.
- [ ] Obligation `Coq(L) ⟺ formula_rep …` proved, axiom-clean.
