# Leg 1 — build instructions (Rocq 9.0 route)

The Coq-8.20 coq-elpi path is a dependency trap (see README §3). Leg 1 builds on an
**isolated Rocq-9.0 switch**, where rocq-elpi 3.4.0 / HB 1.10.2 / MathComp 2.5 build cleanly.

## Switch (one-time)
```sh
opam switch create dualtp-leg1-r9 ocaml-base-compiler.4.14.2 -y
opam repo add rocq-released https://rocq-prover.org/opam/released --switch dualtp-leg1-r9 -y
opam repo add coq-released  https://coq.inria.fr/opam/released   --switch dualtp-leg1-r9 -y
opam install --switch dualtp-leg1-r9 -y \
  coq.9.0.1 coq-elpi coq-mathcomp-ssreflect coq-equations coq-stdpp coq-ext-lib
```

## Semantics + leg-1 proof
The vendored `joscoh/why3-semantics` (rocq-9.0 branch, pinned) must be built OUTSIDE the
macsl tree (macsl/dune-project otherwise captures it as its workspace root). Build copy:
```sh
cp -r why3-semantics /tmp/why3sem && cp -r leg1 /tmp/why3sem/leg1   # SeparatedTrans.v + dune
mv /tmp/why3sem/leg1/dune.leg1-theory /tmp/why3sem/leg1/dune
eval "$(opam env --switch=dualtp-leg1-r9 --set-switch)"
cd /tmp/why3sem && dune build @proofs/core/all leg1/SeparatedTrans.vo -j4   # -> exit 0
```

## Status (this session)
- Toolchain: GREEN (rocq-elpi 3.4.0 etc. — the coq-elpi blocker is bypassed on Rocq 9).
- `proofs/core`: 33/33 .vo (incl. Syntax, Types[HB], Denotational/formula_rep) — no errors.
- `leg1/SeparatedTrans.v`: compiles (exit 0). Confirms substrate usable downstream;
  re-states the coqwp Memory defs in Rocq 9; PROVES `separated_trans_Coq`;
  scaffolds `[[separated_trans]] : formula` against the real Syntax constructors.
- NEXT (§5 steps 3-5): build the `[[separated_trans]]` formula term; round-trip vs
  `why3-separated_trans.mlw`; prove `separated_trans_Coq <-> formula_rep ... [[separated_trans]]`,
  Print-Assumptions-clean.
