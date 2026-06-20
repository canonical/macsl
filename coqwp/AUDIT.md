# `coqwp` trust-surface audit (Frama-C 32.1 / Why3 1.8.2 / Coq 8.20.1)

`coqwp` is the TCB of WP's Coq backend. This audit enumerates what a
`-wp-prover coq` green actually trusts, classifies each item by soundness risk,
and records the hardening roadmap. Counts are from the vendored copy.

## The three kinds of "unproved" thing (they are NOT equal)

1. **`Axiom` (3 total).** All are `WhyType` instances —
   `addr_WhyType` (Memory.v), `rounding_mode_WhyType`, `float_kind_WhyType`
   (Cfloat.v). These assert a Why3 type-class witness (inhabitance/decidable
   equality) for a declared type. Standard and benign; not a behavioural axiom.

2. **`Admitted` *opaque definitions* (~52).** e.g. `Definition region : Z -> Z.
   Admitted.`, `Definition linked …`, `Definition sconst …`, plus many float and
   set operators. These are **abstract symbols with no body** — the Coq
   counterpart of a Why3 *declared* (uninterpreted) symbol. They are **sound**:
   an opaque constant has no axioms relating it to anything, so it cannot prove
   `False`. (It also carries *no information* — see §sconst.)

3. **`Admitted` *lemmas* (~57).** e.g. in `Memory.v`, all 11 are marked
   `(* Why3 goal *)` — Why3 expected a **proof**, and the realization leaves them
   `Admitted`. These are **trusted-but-unproven facts** and *do* enter the TCB:
   every coq green that uses one rests on it. They are the real trust surface.

| File | opaque-def Admitted | **lemma Admitted (trust surface)** |
|---|---|---|
| `Memory.v` | 9 | **11** (all `(* Why3 goal *)`) |
| `Vset.v` | 11 | **11** |
| `Cfloat.v` | 30 | **32** |
| `ArcTrigo.v` | 2 | **2** |
| `ExpLog.v` | 0 | **1** |

The 11 memory lemmas (most relevant to typical WP proofs):
`separated_1`, `separated_included`, `separated_trans`, `eqmem_included`,
`eqmem_sym`, `havoc_access`, `int_of_addr_bijection`, `addr_of_int_bijection`,
`addr_of_null`, `table_to_offset_zero`, `table_to_offset_monotonic`.
They are standard, almost certainly true, and SMT-validated in the Why3 theory —
but in **Coq** they are admitted. A `-wp-prover coq` result is sound only modulo
these. `Print Assumptions wp_goal` (per generated `.v`) shows which ones a given
green actually depends on.

## Why we did NOT patch `sconst` to close the strncpy goal (a rigor decision)

The open goal `log_transfer_call_strncpy_2_requires_valid_nstring_src`
(`../tests/small_example/coq/`) needs `is_sint8` of the string's char bytes. The
tempting "fix" is to give `sconst` a definition that implies it. **That would be
unsound**, and the reasoning is the heart of this audit:

- In WP's Why3 theory (`wp/why3/frama_c_wp/memory.mlw`), `sconst` is an
  **abstract predicate with no definition**: `predicate sconst (map addr int)`.
  WP emits `sconst t3` as a **content-free tag**; no backend derives anything
  from it.
- Realizing `sconst` in Coq to imply `is_sint8` would **assert content WP never
  established** — i.e. smuggle an axiom into the TCB. One wrong axiom makes every
  coq green vacuous: the exact opposite of rigor.
- The genuine fact (`is_sint8` of a char) **is** sound, but WP supplies it
  **per char read** (a hypothesis `is_sint8 x` at each load — verified on
  `int read_char(char*s){return s[0];}`). It is **not** a property of the raw
  `addr→Z` map; a blanket `∀ (m:addr→Z) p, … → is_sint8 (m p)` would be unsound
  because the *int* chunk is also an `addr→Z` map (chunk-typing is erased in the
  Coq encoding).
- This particular VC frames `valid_read_nstring` without *reading* the bytes, so
  no `is_sint8` is in scope. The only **sound** closes are a change in WP's
  **goal generation** (emit `is_sint8` for the strlen bytes — a Frama-C OCaml
  change) or a **C-side dissolve** (don't copy two caller strings). Not coqwp.

**Rule.** Never realize an abstract Why3 symbol with content in order to close a
goal. Realize a symbol only to *match* its Why3 definition; **prove** (`Qed`)
the Why3 *goals*; **admit** only Why3 *assumptions*, and document them here.

## Hardening roadmap (turn trust into proof)
1. Prove the 11 `Memory.v` `(* Why3 goal *)` lemmas in this vendored copy
   (`separated_*`, `eqmem_*`, the addr bijections, `table_to_offset_*`) → `Qed`.
2. Then `Vset.v` (11) and the float lemmas (`Cfloat.v`, 32).
3. Add a CI check: `Print Assumptions` on each macsl coq green must list only
   intended `coqwp` items, and the audited-as-proved set must not regress.
