# Vendored `coqwp` — the WP Coq-backend trust root

A verbatim copy of Frama-C/WP's Coq realizations,
`$(frama-c -print-share-path)/wp/coqwp/`, taken from **Frama-C 32.1 (Germanium)**
(Why3 1.8.2 / Coq 8.20.1, the `framac-coq8` switch). Origin: CEA, **LGPL-2.1**
(same licence as macsl).

## What this is
When WP discharges a goal with `-wp-prover coq`, it emits a `.v` per goal that
`Require`s these files. They are the **Coq realizations** of WP's Why3 theories —
the abstract symbols and axioms of WP's logic given concrete Coq definitions and
(where Why3 expects it) proofs:

| File(s) | Realizes |
|---|---|
| `Memory.v` | the memory model: `addr` (base/offset), `separated`, `valid_rd/rw`, `memcpy`, `region`, `linked`, `sconst` |
| `Cint.v` `Cbits.v` `Zbits.v` `Bits.v` | machine integers: `to_sint8`/`is_sint8`/…, two's-complement & bitwise ops |
| `Cfloat.v` `Cmath.v` `ExpLog.v` `Square.v` `ArcTrigo.v` | reals / floats |
| `Vset.v` `Vlist.v` | ACSL sets and logic lists |
| `Qed.v` `Qedlib.v` | WP's Qed term-engine lemmas |
| `bool/ int/ map/ real/` | the Why3 standard library, realized for Coq |

## Why vendor it (extreme rigor)
`coqwp` is the **trusted computing base** of every `-wp-prover coq` result: a
green rests on these realizations being consistent. An auditable, version-
controlled copy lets us (a) **review** that trust surface and (b) **harden** it
(turn admitted lemmas into proofs). See **`AUDIT.md`** for the trust-surface
audit and the hardening roadmap.

This copy is currently **verbatim / unmodified** — see `AUDIT.md` §"Why we did
not patch `sconst`" for why the open `strncpy`/`valid_read_nstring` goal is *not*
closed by a realization change (doing so would be unsound).

## Using a custom coqwp with WP
WP's share directory (which **contains** `coqwp/`, `why3/`, and `*.driver`) is
overridden with **`-wp-share <dir>`**. So to run WP against a *patched* coqwp:

1. vendor the **whole** wp share (`cp -r $(frama-c -print-share-path)/wp wp-share`),
   replacing `wp-share/coqwp` with this directory (or your patched version);
2. **recompile** the realizations to `.vo` against the Why3 Coq stdlib, e.g.
   `coqc -R "$(why3 --print-libdir)/coq" Why3 -R wp-share/coqwp "" Memory.v …`
   (respect inter-file dependencies; `BuiltIn`→`Qedlib`→`Memory`→…);
3. run `frama-c -wp -wp-prover coq -wp-share wp-share …`.

Build artifacts (`.vo/.vos/.vok/.glob/.aux`) are git-ignored; only the `.v`
sources are tracked.

## Audit discipline
Every `-wp-prover coq` green should be checked with **`Print Assumptions
wp_goal`** in its `.v`: it lists exactly which `coqwp` admitted lemmas / opaque
symbols the proof depends on. A green that leans on an admitted `(* Why3 goal *)`
lemma is sound only insofar as that lemma is — which is the point of `AUDIT.md`.
