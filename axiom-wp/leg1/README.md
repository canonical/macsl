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

**Update — no version split (good news).** The upstream repo has a **`coq-8.20`
branch**: the semantics builds under **Coq 8.20.1** (Equations 1.3.1+8.20, MathComp
2.3.0, std++ 1.11.0, coq-ext-lib 0.13.0) — the *same* Coq as coqwp. So leg 1 does
NOT need a separate Rocq-9 dev; the re-stated Memory defs (or the coqwp ones) live
in one Coq world. `Types.v` uses `HB.instance` (Hierarchy Builder), so **MathComp
2.x is required** (1.x won't do — checked).

**BLOCKED (this session) — coq-elpi cannot build its native plugin here.** The full
build was attempted in a dedicated `dualtp-sem` switch (Coq 8.20.1 + Equations +
std++ + ext-lib all install fine). But **`coq-elpi` fails to build** — identically
across **2.3.0, 2.5.2, and rocq-elpi 3.2.0**:
`System error: ".../rocq-elpi/elpi/elpi_plugin.cmxs: No such file or directory"`.
It is **environmental and version-independent** (not a leg-1 flaw): `ocamlopt.opt`
is present and works, but coq-elpi's dune build never links the plugin `.cmxs`
(`COQ_NATIVE_COMPILER_DEFAULT=no`). Since MathComp 2.x → Hierarchy Builder →
coq-elpi, this transitively blocks building the semantics, hence `formula_rep`,
hence the leg-1 obligation. **Resolution path:** build in an environment where
coq-elpi/MathComp are prebuilt (the **Coq Platform** bundle, or a CI image with the
platform), then resume at §4–§5. Everything *else* for leg 1 is grounded and ready.

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

## 5. Next steps (resume here once coq-elpi/MathComp build, e.g. on Coq Platform)
1. In an environment with **prebuilt** coq-elpi + MathComp 2.3.0 (Coq Platform
   8.20, or a CI image), `opam install coq-equations.1.3.1+8.20
   coq-mathcomp-ssreflect.2.3.0 coq-stdpp.1.11.0 coq-ext-lib.0.13.0`.
2. Vendor the **full** `joscoh/why3-semantics` **`coq-8.20` branch** at a pinned
   commit under `axiom-wp/why3-semantics/` (mind licence/attribution); `make proofs`.
3. Read the real `Syntax.v` `formula`/`term` constructors (already mapped:
   `Fquant Tforall` / `Fbinop Timplies` / `Fpred` / `Tfun`); write
   `⟦separated_trans⟧ : formula` (the AST→`formula` bridge for this lemma).
4. Add the bridge **round-trip check** (pretty-print the `formula` back through
   Why3, diff vs `why3-separated_trans.mlw`) — spec §5.8, fail-closed.
5. Prove the §4 obligation `Coq(L) ⟺ formula_rep …`; confirm axiom-clean
   (`Print Assumptions` ⊆ `A_coq`).
6. Wire a fail-closed `leg1/check.sh` + a CI job; flip `Memory.separated_trans`'s
   `crosscheck` status toward certified.

## Status
- [x] Ground-truth `Why3(L)` extracted; Why3≡Coq≡Lean confirmed by inspection.
- [x] Fragment coverage: **PASS** (in-fragment); MathComp 2.x required (`HB.instance`).
- [x] Toolchain: **coq-8.20 branch found** — semantics builds on Coq 8.20.1 (no
      Rocq-9 split). Coq + Equations + std++ + ext-lib install fine.
- [ ] Full semantics built. **BLOCKED: coq-elpi `.cmxs` fails to build in this
      environment (2.3.0/2.5.2/3.2.0, identical, env-not-version) → MathComp 2.x →
      semantics blocked. Resolve on Coq Platform / a prebuilt-coq-elpi image (§3, §5).**
- [ ] `⟦separated_trans⟧` `formula` term + bridge round-trip.
- [ ] Obligation `Coq(L) ⟺ formula_rep …` proved, axiom-clean.
