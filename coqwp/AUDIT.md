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

## Hardening DONE: `Memory.v`'s 11 lemmas (see `Memory_hardened.v`)

All 11 `(* Why3 goal *)` lemmas `Memory.v` leaves `Admitted` are now **proved in
Coq 8.20** in `Memory_hardened.v`, and `Print Assumptions` reports **"Closed
under the global context"** for every one — **zero axioms, zero admits**.

Build & re-audit:
```sh
coqc -R "$(why3 --print-libdir)/coq" Why3 Memory_hardened.v     # exit 0
# then: Print Assumptions <lemma>.  ->  Closed under the global context  (x11)
```

Note `coqwp` itself does **not** build on Coq 8.20 (it uses `omega`, removed in
8.12), so `Memory_hardened.v` is **self-contained**: it re-states the relevant
definitions **verbatim** from `Memory.v` and uses `lia`. Two strengths of result:

- **Proved OUTRIGHT (5)** — over the verbatim concrete definitions, so these are
  unconditional theorems exactly matching `Memory.v`'s lemmas:
  `separated_1`, `separated_included`, `separated_trans`, `eqmem_included`,
  `eqmem_sym`. (`eqmem` models `farray` by its access function — `Map.map a b :=
  a -> b` — which is faithful for these lemmas; the record's whytype metadata is
  irrelevant.) Also re-proves the helper `included_trans`.
- **Proved for a SOUND WITNESS realization (6)** — the symbol is abstract in
  `Memory.v`, so the admitted lemma is its *defining axiom*; proving it for a
  concrete witness shows the axiom is **consistent / satisfiable** (sound to
  assume), which is the rigor goal for an abstract symbol:
  `havoc_access` (realize `havoc` via a decidable `separated`),
  `table_to_offset_zero`/`monotonic` (realize `table_to_offset` as identity),
  `int_of_addr_bijection`/`addr_of_int_bijection`/`addr_of_null` (realize the
  `addr ↔ Z` pair via a `Z ↔ nat` bijection + stdlib `Cantor`).

## Hardening DONE: `Vset.v`'s 11 lemmas (see `Vset_hardened.v`)

All 11 `(* Why3 goal *)` lemmas `Vset.v` leaves `Admitted` are proved in
`Vset_hardened.v`. `Vset` declares *all* its set symbols abstract, so this is a
**sound witness realization**: `set a := a -> bool` (a decidable-membership
characteristic function; `singleton` uses `WhyType`'s decidable equality).
Proving each lemma for this model shows `Vset`'s admitted axioms are
consistent/satisfiable.

`Print Assumptions`: **9 of 11 are "Closed under the global context"**; the two
**set-equality** lemmas `union_empty` and `inter_empty` depend on
`functional_extensionality` — a standard Coq axiom, and exactly what `Qedlib`
itself assumes (`Hypothesis extensionality`, used by `farray_eq`). No other axiom
appears. `check.sh` whitelists `functional_extensionality` for `Vset` only.

## Hardening roadmap (remaining)
1. ~~`Memory.v` (11)~~ **done** (`Memory_hardened.v`, axiom-free).
2. ~~`Vset.v` (11)~~ **done** (`Vset_hardened.v`; 9 axiom-free, 2 via
   `functional_extensionality`).
3. The float lemmas (`Cfloat.v`, 32) and `ArcTrigo.v` (2), `ExpLog.v` (1).
4. CI: run `./check.sh` — it asserts each lemma is `Closed under the global
   context` or (Vset only) depends solely on the whitelisted
   `functional_extensionality`; no regression of the proved set.
