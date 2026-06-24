# macsl

[![axiom-wp dual-TP](https://github.com/canonical/macsl/actions/workflows/axiom-wp.yml/badge.svg)](https://github.com/canonical/macsl/actions/workflows/axiom-wp.yml)

macsl is a Frama-C plugin that checks HAPPY properties (Hyperproperty Analysis for
Program PolicY). It supports the six [STRIDE](https://en.wikipedia.org/wiki/STRIDE_model)
families. You state a global confinement property once, and macsl instruments every
matching site with an ACSL `assert` that WP discharges.

It is a standalone re-spin of CEA's [MetAcsl](https://git.frama-c.com/pub/meta)
meta-property mechanism, licensed LGPL-2.1 (inherited from MetAcsl). It also reduces the
Trusted Computing Base (TCB) by proving the Coq realization lemmas that WP relies on; see
[Trusted Computing Base](#trusted-computing-base-coqwp) below.

## Status

HAPPY connects high-level security analysis such as
[EBIOS RM](https://messervices.cyber.gouv.fr/guides/en-ebios-risk-manager-method) or
[Risk Management Framework](https://csrc.nist.gov/projects/risk-management/about-rmf) to the
code.

All seven HAPPY policies are supported, covering the six STRIDE families:

- `\context(\writing)` — H-T, write confinement
- `\context(\reading)` — H-I1, read confinement
- `\context(\postcond)` — H-R, audit-log completeness and append-only; H-E, privilege
  monotonicity via a `\diff` gate exemption
- `\context(\precond)` — H-S, check-before-use capabilities
- `\context(\noninterference)` — H-I2, noninterference via synthesized self-composition
- `\context(\total)` — H-D, denial-of-service / totality: a `terminates` clause WP
  discharges from loop variants, plus an `-wp-rte` no-fault bundle

It builds and is verified against Frama-C 32.1 (Germanium); `./tests/run.sh` passes
(34/34). The roadmap is in [`docs/happy-roadmap.md`](docs/happy-roadmap.md); the design rationale is
in [`docs/macsl-impl.md`](docs/macsl-impl.md).

### Worked example

[`tests/small_example`](tests/small_example) is a small banking server used as an
end-to-end example. What carries trust here is the verification result: every HAPPY policy
below is discharged by Frama-C/WP and can be re-checked by re-running the proofs. The
verdicts rest on the proof obligations the prover discharges, not on how the annotations
were written.

The example pairs an EBIOS RM risk study with the matching machine-checked verdicts; the
conformance report is [`ebios-crosswalk.md`](tests/small_example/ebios-crosswalk.md). So
that the threat model is not shaped by the implementation it is supposed to assess, the
risk study was developed from the system's mission and specification independently of the
source, then reviewed and signed off by a human risk owner.

Comparing the study against the verification surfaced three gaps:

- **FE10 — silent audit saturation** (G4, High). `nonrepud_complete` is proved only under
  `requires 0 <= audit_len < 1024`. The feared case (log full, transfers still succeeding
  unlogged) falls outside the proved envelope: the precondition assumes it away.
- **FE2 — horizontal RBAC** (G4, High). "A user may debit only their own account" is
  enforced in `transfer`'s body but was not asserted as a HAPPY hyperproperty, so it was
  code-enforced rather than machine-verified.
- **FE11 — token lifecycle** (G3, Moderate). Expiry, revocation, and query-string leakage
  are the declared trusted boundary: a scope limit, not a defect.

Remediation (each gap chosen for closure by a human):

- FE10: transactions now close when the audit log is full.
- FE2: a HAPPY policy now asserts the horizontal-RBAC rule (a role-2 caller may debit only
  their own account) as a WP-discharged hyperproperty; the matching attack goes RED. See
  [`rbac_horizontal.c`](tests/small_example/rbac_horizontal.c).
- FE11: a new H-S policy `token_live` (a revoked, expired, or replayed token cannot
  authorize an operation) is proved 8/8 on
  [`token_lifecycle.c`](tests/small_example/token_lifecycle.c), with a red replay control
  in [`attacks.c`](tests/small_example/attacks.c).

## Real-world use case — Mbed TLS 4.1.0

The same pipeline run end-to-end on a real codebase (reports in
[`real-use-case/`](real-use-case)): a **code-blind EBIOS RM** study
([`mbedtls-ebios-report.md`](real-use-case/mbedtls-ebios-report.md)) drives a `frama-c-launch`
campaign — RTE/functional verdicts on the X.509/ASN.1 parser queue
([`mbedtls-found-issues.md`](real-use-case/mbedtls-found-issues.md): no genuine defects; the
undischarged goals are missing-precondition `mem_access` timeouts), and the EBIOS↔verification
coverage join ([`mbedtls-ebios-gaps.md`](real-use-case/mbedtls-ebios-gaps.md)): 2 feared events
RTE-covered, **5 BLOCKED residuals** (crypto/entropy/negotiation/side-channel — out of WP reach),
and **4 Tier-3 logic risks discharged as HAPPY hyperproperties**, machine-checked green on a
focused driver (the same compliant-core + red-control discipline as `small_example`):

```
┌───────────────────┬───────────────┬───────────────────────────────────┬───────────┬────────────────────────┐
│      Policy       │    Family     │               EBIOS               │ Compliant │      Attack (red)      │
├───────────────────┼───────────────┼───────────────────────────────────┼───────────┼────────────────────────┤
│ verdict_integrity │ H-T (T)       │ FE2 trust-decision integrity      │ ✅        │ tamper_verdict         │
├───────────────────┼───────────────┼───────────────────────────────────┼───────────┼────────────────────────┤
│ accept_checked    │ H-S (S)       │ FE2 accept-after-checks           │ ✅        │ unchecked_accept       │
├───────────────────┼───────────────┼───────────────────────────────────┼───────────┼────────────────────────┤
│ hs_sequence       │ H-S (S)       │ FE1/FE6 state-machine sequencing  │ ✅        │ confused_state         │
├───────────────────┼───────────────┼───────────────────────────────────┼───────────┼────────────────────────┤
│ resumption_conf   │ H-I1 (I)      │ FE4 resumption-secret confinement │ ✅        │ leak_resumption        │
├───────────────────┼───────────────┼───────────────────────────────────┼───────────┼────────────────────────┤
│ seqno_monotonic   │ H-R/H-E (R/E) │ FE5 anti-replay                   │ ✅        │ accept_record rollback │
└───────────────────┴───────────────┴───────────────────────────────────┴───────────┴────────────────────────┘
```

The compliant driver proves **41/41** (the 5 policies = 19 instrumented assertions, + RTE); the
attack driver leaves exactly **5** goals unproved, one per policy (non-vacuity). EBIOS W5
residual-risk sign-off is **pending** (the human risk owner). The verification overlay (drivers,
config, baseline pin, scope map) lives at the use-frama-c root in `mbedtls-acsl/`.

## Trusted Computing Base (coqwp)

A `-wp-prover coq` "Valid" is only as trustworthy as the Coq realization library (`coqwp`)
that WP inlines: that library is the TCB of every Coq-discharged goal. Stock Frama-C ships
it with a large unproven trust surface; macsl proves it out. This is a second benefit on
top of the HAPPY policy language. Full classification is in
[`axiom-wp/coqwp/AUDIT.md`](axiom-wp/coqwp/AUDIT.md); the CI gate is
[`axiom-wp/coqwp/check.sh`](axiom-wp/coqwp/check.sh) plus `.github/workflows/axiom-wp.yml`.

Stock `coqwp` carries 111 raw `Admitted`, but they are three different things and only one
is an assumed fact:

| Kind | Count | A trusted fact? |
|---|---|---|
| `WhyType` axioms (type-class witnesses) | 3 | No — standard, benign |
| Opaque-definition `Admitted` (uninterpreted symbols, no body) | ~52 | No — sound by construction (no body cannot prove `False`) |
| Trust-bearing `Admitted` lemmas (`(* Why3 goal *)`) | 57 | Yes — the trust surface |

macsl proves all 58 trust-bearing lemmas (the 57 above plus the π bound) in admit-free
`*_hardened.v` twins, gated per file by `check.sh` (no `Admitted`/`admit`; compiles; every
lemma is `Closed under the global context` or uses only whitelisted standard axioms):

| File | Lemmas | Result |
|---|---|---|
| `Memory_hardened.v` | 11 | zero axioms (Closed under the global context) |
| `Vset_hardened.v` | 11 | 9 zero-axiom, 2 via `functional_extensionality` |
| `Cfloat_hardened.v` | 32 | no admits, no custom axioms; 2 standard Reals axioms |
| `ArcTrigo_hardened.v` | 2 | Coq stdlib `asin`/`acos`; 2 standard Reals axioms |
| `ExpLog_hardened.v` | 1 | Coq stdlib `exp`; 2 standard Reals axioms |
| `Trigonometry_hardened.v` | 1 | `Pi_double_precision_bounds` via CoqInterval; standard classical, Reals, and `PrimInt63` axioms |

The only axioms relied on are standard Coq foundations: `functional_extensionality` (which
`Qedlib` itself assumes), `sig_forall_dec`/`sig_not_dec` (Coq's `ℝ` is itself axiomatized),
classical logic, and Coq's native 63-bit integer primitives (`PrimInt63`/`Uint63`, used by
CoqInterval's reflective computation). There are no custom or behavioural axioms.

| | Stock Frama-C | macsl |
|---|---|---|
| Unproven trust-bearing lemmas | 58 | 0 (CI-gated) |
| Custom/behavioural axioms | 0 | 0 |

The last open lemma, `real/Trigonometry.v::Pi_double_precision_bounds` (a 1-ulp-at-2⁻⁵¹
bracket on π that the upstream realization stubbed out to avoid a dependency on
CoqInterval), is now proved with CoqInterval, in both `Trigonometry_hardened.v` and the
patched original (`Qed`, no stub; the original gains a build-time `coq-interval`
dependency).

### Lean cross-validation (58 of 58 twins)

Every trust-bearing lemma also has a verified Lean twin, under `axiom-wp/leanwp/` and gated
by `leanwp/check.sh` and `leanwp/realfloat/check.sh` (no `sorry`; axioms a subset of
`propext`, `Classical.choice`, `Quot.sound`): `Memory` 11, `Vset` 11, `Cfloat` 32,
`ArcTrigo` 2, `ExpLog` 1, and the π bound. `Pi_double_precision_bounds` is discharged from
mathlib's 20-digit bracket (`Real.pi_gt_d20`/`Real.pi_lt_d20`), well inside the 2⁻⁵¹ window.
See [`axiom-wp/DUALTP-STATUS.md`](axiom-wp/DUALTP-STATUS.md) for the `Why3 ≡ Coq ≡ Lean`
3-way structural check status.

## Two toolchains: Coq 8.20.1 (coqwp) and Rocq 9.0 (leg-1)

macsl uses two distinct Coq/Rocq toolchains for two distinct concerns (the Coq-to-Rocq
rename happened at 9.0, so 8.20.1 is still "Coq" and 9.x is "Rocq"):

- **Coq 8.20.1** is the coqwp trust root (the `*_hardened.v` files, including the π bound
  proved with CoqInterval). It must match Frama-C 32.1's WP Coq realization library, which
  is the TCB of every `frama-c -wp-prover coq` green, so it is pinned to Coq 8.20.1 / Why3
  1.8.2.
- **Rocq 9.0** is used for the leg-1 dual-TP semantic anchoring (`leg1/Model.v` plus the
  vendored `joscoh/why3-semantics`). Rocq 9 is required here because that formalization
  needs MathComp 2.x, Hierarchy Builder, and coq-elpi, which will not build on the Coq-8.20
  pin. It lives in a separate, isolated opam switch (`leg1/BUILD.md`) and never touches the
  8.20 toolchain.

| Concern | Toolchain | CI-gated? |
|---|---|---|
| coqwp trust root incl. π (`*_hardened.v`) | Coq 8.20.1 + coq-interval 4.11.4 | Yes — `axiom-wp.yml` `coq` job |
| leg-1 dual-TP semantic anchoring (`Model.v`) | Rocq 9.0 + coq-elpi / MathComp 2.5 | Yes — `axiom-wp.yml` `leg1` job builds the semantics + model and the closed obligations: the theorems `sep_trans_faithful`, `included_trans_faithful`, `sep_incl_faithful` (`formula_rep … = true ↔ …_prop`), axiom-clean. Combined with leg 2 (`dualtp/`), `Memory.separated_trans`, `Memory.included_trans`, and `Memory.separated_included` are dual-TP **certified**. |

## Quick start

```sh
eval $(opam env --switch=framac-coq8)
dune build
# run the test suite:
./tests/run.sh
# use it on your own file (autoload disabled to avoid an installed MetAcsl
# clashing on shared ACSL builtins; see docs/usage.md):
frama-c -no-autoload-plugins -load-plugin wp \
        -load-module _build/default/src/macsl.cmxs \
        -macsl -wp -wp-rte your.c
```

## A policy

```c
int secret = 0, pub = 0;

/*@ happy \prop, \name("iso"), \targets(\ALL),
      \context(\writing), \separated(\written, &secret);   // nothing WRITES `secret`  (H-T)
*/
/*@ happy \prop, \name("conf"), \targets(\ALL),
      \context(\reading), \separated(\read, &secret);      // nothing READS `secret`   (H-I1)
*/

void f(void) { pub = secret; secret = 2; }
// `pub = secret` -> the read assert is RED ; `secret = 2` -> the write assert is RED
```

See [docs/usage.md](docs/usage.md) for the full surface and options, and
[glossary/glossary.md](glossary/glossary.md) for terminology.
