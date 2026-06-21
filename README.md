# macsl

[![axiom-wp dual-TP](https://github.com/canonical/macsl/actions/workflows/axiom-wp.yml/badge.svg)](https://github.com/canonical/macsl/actions/workflows/axiom-wp.yml)

**macsl** is a Frama-C plugin that checks **HAPPY** properties. Happy stands for Hyperproperty Analysis for Program
PolicY. The six [STRIDE](https://en.wikipedia.org/wiki/STRIDE_model) families are supported. The principle is
to state a global write-confinement property once, and macsl instruments every matching
write site with an ACSL `assert`, which WP discharges.

It is a standalone re-spin of CEA's [MetAcsl](https://git.frama-c.com/pub/meta) meta-property
mechanism. Licence is LGPL-2.1, inherited from MetAcsl. The Trusted Computing Based (TCB) has
been reduced by proving several lemmas in coqwp.

## Status

HAPPY enables to bridge the gap between high level security analysis such as
[EBIOS RM](https://messervices.cyber.gouv.fr/guides/en-ebios-risk-manager-method) and the code.

**All seven HAPPY policies — the full six [STRIDE](https://en.wikipedia.org/wiki/STRIDE_model) families**:
`\context(\writing)` (**H-T**, write confinement), `\context(\reading)` (**H-I1**, read
confinement), `\context(\postcond)` (**H-R**, audit-log completeness + append-only; **H-E**,
privilege monotonicity via `\diff` gate exemption), `\context(\precond)` (**H-S**, check-before-use
capabilities), `\context(\noninterference)` (**H-I2**, noninterference via synthesized
self-composition), and `\context(\total)` (**H-D**, denial-of-service / totality: a `terminates`
clause WP discharges from loop variants + an `-wp-rte` no-fault bundle). Builds and is verified
against **Frama-C 32.1 (Germanium)**; `./tests/run.sh` is green (34/34). The roadmap is in
[`happy-roadmap.md`](happy-roadmap.md); the design rationale is [`macsl-impl.md`](macsl-impl.md).

A [flagship example](tests/small_example) simulating a banking system is available:

- The [EBIOS RM risk report](tests/small_example/ebios-report.txt) for the core-banking server, was authored by a code-blind agent from the spec's mission alone and hardened by a disjoint code-blind reviewer, leaving only human risk-owner sign-off outstanding.

- Then two nested loops of agents annotated the code and generated the [conformance report](tests/small_example/ebios-crosswalk.md).
Three gaps were spotted after the first iteration of the loop:
    - FE10 silent audit saturation (G4, High) — headline. nonrepud_complete is proved only under `requires 0 <= audit_len < 1024`. The EBIOS-feared case — log full, transfers keep succeeding unlogged — is outside the proved envelope; the precondition assumes the threat away.
    - FE2 horizontal RBAC (G4, High). "A User may debit only their own account" is enforced in transfer's body but is not asserted as a HAPPY hyperproperty — code-enforced, not machine-verified.
    - FE11 token lifecycle (G3, Moderate). Expiry/revocation/query-string leakage are the declared trusted boundary — honest scope limit, not a defect.


Closing FE10 "silent audit saturation" was chosen by a human and led to closing transactions when the log is full.

Closing FE2 "horizontal RBAC" meant adding a HAPPY policy that asserts the horizontal-RBAC rule ("a role-2 caller may debit only their own account") as a WP-discharged hyperproperty — confirming the matching attack goes RED. That lead to the creation of [rbac_horizontal.c](tests/small_example/rbac_horizontal.c) by the loop of agents.

Closing FE11's meant adding a new verified H-S policy `token_live` (a revoked/expired/replayed token cannot authorize an operation, proved 8/8 on [token_lifecycle.c](tests/small_example/token_lifecycle.c) with a red replay control in [attacks.c](tests/small_example/attacks.c)),


## Trusted Computing Base — the Coq work (a smaller TCB than legacy Frama-C)

A `-wp-prover coq` "Valid" is only as trustworthy as the **Coq realization library** (`coqwp`) WP
inlines — that library *is* the TCB of every Coq-discharged goal. Stock Frama-C ships it with a large
unproven trust surface; macsl closes it. This is a second, independent benefit of macsl on top of
legacy Frama-C (the first being the HAPPY policy language above). Full classification:
[`axiom-wp/coqwp/AUDIT.md`](axiom-wp/coqwp/AUDIT.md); CI gate: [`axiom-wp/coqwp/check.sh`](axiom-wp/coqwp/check.sh)
+ `.github/workflows/coqwp.yml`.

**The trust surface, audited.** Stock `coqwp` carries **111 raw `Admitted`**, but they are three
different things — only one is a real assumed fact:

| Kind | Count | A trusted *fact*? |
|---|---|---|
| `WhyType` axioms (type-class witnesses) | 3 | No — standard, benign |
| Opaque-definition `Admitted` (uninterpreted symbols, no body) | ~52 | No — sound by construction (no body ⇒ cannot prove `False`) |
| **Trust-bearing `Admitted` *lemmas*** (`(* Why3 goal *)`) | **57** | **Yes — the real trust surface** |

**What macsl proves.** All **58** trust-bearing lemmas are machine-checked in admit-free
`*_hardened.v` twins, gated per-file by `check.sh` (no `Admitted`/`admit`; compiles; every lemma
`Closed under the global context` or only whitelisted *standard* axioms):

| File | lemmas | result |
|---|---|---|
| `Memory_hardened.v` | 11 | **zero axioms** (Closed under the global context) |
| `Vset_hardened.v` | 11 | 9 zero-axiom + 2 via `functional_extensionality` |
| `Cfloat_hardened.v` | 32 | no admits / no custom axioms; 2 standard Reals axioms |
| `ArcTrigo_hardened.v` | 2 | genuine (Coq stdlib `asin`/`acos`); 2 standard Reals axioms |
| `ExpLog_hardened.v` | 1 | genuine (Coq stdlib `exp`); 2 standard Reals axioms |
| `Trigonometry_hardened.v` | 1 | `Pi_double_precision_bounds` via CoqInterval; standard classical + Reals + `PrimInt63` axioms |

The only axioms relied on are **standard Coq foundations** — `functional_extensionality` (what
`Qedlib` itself assumes), `sig_forall_dec`/`sig_not_dec` (Coq's `ℝ` is *itself* axiomatized),
classical logic and Coq's native 63-bit integer primitives (`PrimInt63`/`Uint63`, used by CoqInterval's
reflective computation) — **no custom or behavioural axioms**.

**Net result:**

| | stock Frama-C | macsl |
|---|---|---|
| Unproven trust-bearing lemmas | **58** | **0** (CI-gated) |
| Custom/behavioural axioms | 0 | 0 |

The last open lemma — `real/Trigonometry.v::Pi_double_precision_bounds` (a 1-ulp-at-2⁻⁵¹ bracket on π
the upstream realization stubbed out "to avoid a dependency on CoqInterval") — is now **proved with
CoqInterval**, in both `Trigonometry_hardened.v` and the patched original (`Qed`, no stub; the original
gains a build-time `coq-interval` dependency). The remaining work is the parallel **Lean**
cross-validation (`axiom-wp/leanwp/`, [`axiom-wp/DUALTP-STATUS.md`](axiom-wp/DUALTP-STATUS.md)): a
future `Why3 ≡ Coq ≡ Lean` 3-way check.

## Two toolchains: Coq 8.20.1 (coqwp) and Rocq 9.0 (leg-1)

macsl uses **two distinct Coq/Rocq toolchains** for two distinct concerns — don't conflate them
(the Coq→Rocq rename happened at **9.0**; `8.20.1` is still legitimately "Coq", `9.x` is "Rocq"):

- **Coq 8.20.1** — the **coqwp trust root** (the `*_hardened.v` files, incl. the π bound proved with
  CoqInterval). This must match **Frama-C 32.1**'s WP Coq realization library — that is the TCB of
  every `frama-c -wp-prover coq` green — so it is pinned to Coq 8.20.1 / Why3 1.8.2.
- **Rocq 9.0** — the **leg-1 dual-TP semantic anchoring** (`leg1/Model.v` + the vendored
  `joscoh/why3-semantics`). We use Rocq 9 here *only because we must*: that formalization needs
  MathComp 2.x → Hierarchy Builder → coq-elpi, which will not build on the Coq-8.20 pin. It lives in
  a **separate, isolated opam switch** (`leg1/BUILD.md`) and never touches the 8.20 toolchain.

| Concern | Toolchain | CI-gated? |
|---|---|---|
| coqwp trust root incl. π (`*_hardened.v`) | Coq 8.20.1 + coq-interval 4.11.4 | ✅ `axiom-wp.yml` **`coq`** job |
| leg-1 dual-TP semantic anchoring (`Model.v`) | Rocq 9.0 + coq-elpi / MathComp 2.5 | ✅ `axiom-wp.yml` **`leg1`** job — builds the semantics + model (axiom-free); the obligation's final cast-cancellation lemma is documented, not yet a theorem, so this gates the **infrastructure**, not the completed proof |

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
