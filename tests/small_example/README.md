# small_example — the flagship HAPPY/STRIDE target

A banking-style backend (authenticate / transfer / audit over a tiny HTTP layer) and the **HAPPY**
policies that secure it. This is the **flagship example** for `macsl`: it shows the same security
policies (1) attached to **realistic** libc-using code, (2) **proved** on a crisp compliant core, and
(3) **caught going red** on deliberate violations. Those three jobs are split across three `.c` files
on purpose — each is load-bearing; none is redundant.

## The three files and their roles

| File | Role | What it is | `macsl -wp` result |
|---|---|---|---|
| **`main.c`** | **Realistic integration** | A full HTTP server (three routes) using real libc — `strtok`/`strcmp`/`strncpy`, `read`/`write`, `socket`/`accept`, variadic `snprintf`/`sscanf` — carrying the audit log + `log_transfer`. The H-R `nonrepud_complete` policy is checked on its **real `transfer()`**. | `transfer` **51/51** (the policy postcondition discharged *through* Frama-C's ACSL libc + a loop invariant + `log_transfer`'s contract). `log_transfer` body 68/69 — one open `valid_read_nstring` strncpy-frame goal, Coq-escalable. |
| **`banking.c`** | **Compliant core (the positive proof)** | A focused, fully-contracted distillation of `main.c`'s security-relevant core (accounts, audit log, `authenticate`, `log_transfer`, `transfer`) carrying **all four policies**. The unambiguous "every policy holds" artifact. | **18/18** — all green. |
| **`banking_attacks.c`** | **Negative controls (the teeth)** | Four attacks, **one per policy**, each violating exactly one and nothing else. Proves the policies are **non-vacuous** — a green that cannot go red proves nothing. | **25/29** — exactly **four** goals red, one per attack. |

**Why three, not one.** `main.c` answers *"do the policies attach to real-world code?"* (yes — the
libc layer is **not** "out of WP's reach"). `banking.c` answers *"do the policies hold?"* on a core
small enough to be **fully green and unambiguous**. `banking_attacks.c` answers *"do the policies have
teeth?"* — and that question has no home in `main.c`, which is the *compliant* backend and contains no
violations by design. `banking.c` + `banking_attacks.c` are a **matched compliant/attack pair** (same
`#define`s, same policy text); the contrast between 18/18 green and four targeted reds is the actual
assurance argument. Collapsing them would either lose the crisp green control or lose the teeth.

## The policies (proved in `banking.c`, exercised on `main.c`'s real `transfer` for H-R)

| Policy | STRIDE / HAPPY | Context | What it proves |
|---|---|---|---|
| `nonrepud_complete` | **H-R** (Repudiation) | `\postcond` | a balance changed ⇒ the audit log grew |
| `nonrepud_append_only` | **H-R** (Repudiation) | `\postcond` | old audit records are never rewritten |
| `authn` | **H-S** (Spoofing) | `\precond` | `transfer` is callable only on an authenticated session |
| `bal_integrity` | **H-T** (Tampering) | `\writing` (`\diff(\ALL,{transfer})`) | only `transfer` may write a balance |

These four cover three of the six HAPPY families (**H-T, H-R, H-S**). The remaining three — **H-I1**
(read confinement), **H-E** (privilege monotonicity), **H-I2** (noninterference) — are specified in
`../../happy-roadmap.md`, not in this directory.

## The four attacks (caught in `banking_attacks.c`)

| Attack | Violates | Caught as |
|---|---|---|
| `transfer_silent` — moves money, never logs | `nonrepud_complete` (H-R) | `transfer_silent…nonrepud_complete` red |
| `rewrite_audit` — overwrites `audit[0]` | `nonrepud_append_only` (H-R) | `rewrite_audit…nonrepud_append_only` red |
| `tamper` — writes a balance directly | `bal_integrity` (H-T) | `tamper…bal_integrity` red |
| `unauth_endpoint` — calls `transfer` without auth | `authn` (H-S) | `unauth_endpoint_call_transfer_requires_authn` red |

## Run

```sh
eval $(opam env --switch=framac-coq8)
dune build
CMXS=_build/default/src/macsl.cmxs
FC="frama-c -no-autoload-plugins -load-plugin wp -load-module $CMXS -macsl -wp -wp-prover alt-ergo,z3"

# Realistic integration: the H-R policy on main.c's real transfer()
$FC -wp-fct transfer tests/small_example/main.c            # 51/51

# Compliant core: all four policies hold
$FC tests/small_example/banking.c                          # 18/18

# Negative controls: exactly four goals red (one per policy)
$FC tests/small_example/banking_attacks.c                  # 25/29
```

(`banking.c` / `banking_attacks.c` are also cases 24–25 in `../run.sh`. The `main.c` proof-status
detail — including the one Coq-escalable goal — is documented in the header of `main.c` itself.)
