# small_example — a worked HAPPY/STRIDE target

A banking-style backend (authenticate / get_role / transfer over a tiny HTTP layer) and the HAPPY
policies that secure it.

## Files

- **`main.c`** — the full example: an HTTP server with three routes. It now also carries the **audit
  log + `log_transfer`** (non-repudiation), and the **H-R `nonrepud_complete` policy is checked on its
  REAL `transfer()`**: `frama-c -macsl -wp -wp-fct transfer` proves **51/51**, including the policy's
  postcondition — discharged *through* Frama-C's ACSL libc (`strcmp`/`strlen` contracts checked at the
  call sites) plus a loop invariant and `log_transfer`'s contract. So the libc layer is **not** "out of
  WP's reach". (Verifying `log_transfer`'s body too is 68/69; the one open goal is a `valid_read_nstring`
  *frame* limitation on `strncpy`, Coq-escalable — ordinary effort, not the policy. See the proof-status
  note in `main.c`.) `banking.c` below remains the crisp, fully-green core for the attack table:
- **`banking.c`** — a focused, fully-contracted distillation of the security-relevant core (accounts,
  the audit log, `authenticate`, `log_transfer`, `transfer`), with all four policies. This is the
  **compliant** system: `macsl -wp` proves **18/18**.
- **`banking_attacks.c`** — the matching **negative controls**: four attacks, one per policy, each
  caught (`25/29` — exactly four goals red).

## The policies (verified in banking.c)

| Policy | STRIDE | Context | What it proves |
|---|---|---|---|
| `nonrepud_complete` | H-R | `\postcond` | a balance changed ⇒ the audit log grew |
| `nonrepud_append_only` | H-R | `\postcond` | old audit records are never rewritten |
| `authn` | H-S | `\precond` | `transfer` is callable only on an authenticated session |
| `bal_integrity` | H-T | `\writing` (`\diff(\ALL,{transfer})`) | only `transfer` may write a balance |

## The four attacks (caught in banking_attacks.c)

| Attack | Violates | Caught as |
|---|---|---|
| `transfer_silent` — moves money, never logs | H-R completeness | `transfer_silent…nonrepud_complete` red |
| `rewrite_audit` — overwrites `audit[0]` | H-R append-only | `rewrite_audit…nonrepud_append_only` red |
| `tamper` — writes a balance directly | H-T integrity | `tamper…bal_integrity` red |
| `unauth_endpoint` — calls `transfer` without auth | H-S | `unauth_endpoint_call_transfer_requires_authn` red |

## Run

```sh
eval $(opam env --switch=framac-coq8)
dune build
CMXS=_build/default/src/macsl.cmxs
frama-c -no-autoload-plugins -load-plugin wp -load-module $CMXS \
        -macsl -wp -wp-prover alt-ergo,z3 tests/small_example/banking.c          # 18/18
frama-c -no-autoload-plugins -load-plugin wp -load-module $CMXS \
        -macsl -wp -wp-prover alt-ergo,z3 tests/small_example/banking_attacks.c   # 25/29
```
(Both are also cases 24–25 in `../run.sh`.)
