# macsl

**macsl** is a Frama-C plugin that checks **HAPPY** policies — *Hyperproperty Analysis for Program
PolicY*. You state a global write-confinement property once, and macsl instruments **every matching
write site** with an ACSL `assert`, which WP discharges.

It is a standalone re-spin of CEA's [MetAcsl](https://git.frama-c.com/pub/meta) meta-property
mechanism, with one deliberate design change: macsl instruments **in place**, so

```sh
frama-c file.c -macsl -wp
```

works directly. Licence: LGPL-2.1 (inherited from MetAcsl).

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
against **Frama-C 32.1 (Germanium)**; `./tests/run.sh` is green (29/29). The roadmap is in
[`happy-roadmap.md`](happy-roadmap.md); the design rationale is [`macsl-impl.md`](macsl-impl.md).

A [flagship example](tests/small_example) simulating a banking system is available.

-The [EBIOS RM risk report](tests/small_example/ebios-report.txt) for the core-banking server, was authored by a code-blind agent from the spec's mission alone and hardened by a disjoint code-blind reviewer, leaving only human risk-owner sign-off outstanding.

- Then two nested loops of agents annotated the code and generated the [conformance report](tests/small_example/ebios-crosswalk.md).
Three gaps were spotted after the first iteration of the loop:
    - FE10 silent audit saturation (G4, High) — headline. nonrepud_complete is proved only under `requires 0 <= audit_len < 1024`. The EBIOS-feared case — log full, transfers keep succeeding unlogged — is outside the proved envelope; the precondition assumes the threat away.
    - FE2 horizontal RBAC (G4, High). "A User may debit only their own account" is enforced in transfer's body but is not asserted as a HAPPY hyperproperty — code-enforced, not machine-verified.
    - FE11 token lifecycle (G3, Moderate). Expiry/revocation/query-string leakage are the declared trusted boundary — honest scope limit, not a defect.


Closing FE10 "silent audit saturation" was chosen by a human and led to closing transactions when the log is full.

Closing FE2 "horizontal RBAC" meant adding a HAPPY policy that asserts the horizontal-RBAC rule ("a role-2 caller may debit only their own account") as a WP-discharged hyperproperty — confirming the matching attack goes RED. That lead to the creation of [rbac_horizontal.c](tests/small_example/rbac_horizontal.c) by the loop of agents.

Closing FE11's meant adding a new verified H-S policy `token_live` (a revoked/expired/replayed token cannot authorize an operation, proved 8/8 on [token_lifecycle.c](tests/small_example/token_lifecycle.c) with a red replay control in [attacks.c](tests/small_example/attacks.c)),


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
