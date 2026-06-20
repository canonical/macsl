# small_example — the flagship HAPPY/STRIDE target

A banking-style backend (authenticate / transfer / audit over a tiny HTTP layer) and the **HAPPY**
policies that secure it. This is the **flagship example** for `macsl`: it shows the same security
policies (1) attached to **realistic** libc-using code, (2) **proved** on a crisp compliant core, and
(3) **caught going red** on deliberate violations. Those three jobs are split across three `.c` files
on purpose — each is load-bearing; none is redundant.

## The three files and their roles

| File | Role | What it is | `macsl -wp` result |
|---|---|---|---|
| **`main.c`** | **Realistic integration** | A full HTTP server (three routes) using real libc — `strtok`/`strcmp`/`strncpy`, `read`/`write`, `socket`/`accept`, variadic `snprintf`/`sscanf` — carrying the audit log + `log_transfer`. **All four policies are instrumented here on the real code** (H-R `nonrepud_complete`, H-R `nonrepud_append_only`, H-T `bal_integrity`, H-S `authn`). | `nonrepud_complete` **1/1** on `transfer`; `nonrepud_append_only` **proves with `-wp-prover z3 -wp-split`** (full `AuditRecord` equality — a struct, not a scalar); `bal_integrity` **50/50** across the non-exempt functions; `authn` **1/1** (the call-site check in `handle_client`). The *whole file* isn't all-green (the routes need loop invariants + libc specs) — which is exactly why `banking.c` exists. |
| **`banking.c`** | **Compliant core (the positive proof)** | A focused, fully-contracted distillation of `main.c`'s security-relevant core (accounts, audit log, `authenticate`, `log_transfer`, `transfer`) carrying **all four policies**. The unambiguous "every policy holds" artifact. | **18/18** — all green. |
| **`banking_attacks.c`** | **Negative controls (the teeth)** | Four attacks, **one per policy**, each violating exactly one and nothing else. Proves the policies are **non-vacuous** — a green that cannot go red proves nothing. | **25/29** — exactly **four** goals red, one per attack. |

**Why three, not one.** `main.c` answers *"do the policies attach to real-world code?"* (yes — the
libc layer is **not** "out of WP's reach"). `banking.c` answers *"do the policies hold?"* on a core
small enough to be **fully green and unambiguous**. `banking_attacks.c` answers *"do the policies have
teeth?"* — and that question has no home in `main.c`, which is the *compliant* backend and contains no
violations by design. `banking.c` + `banking_attacks.c` are a **matched compliant/attack pair** (same
`#define`s, same policy text); the contrast between 18/18 green and four targeted reds is the actual
assurance argument. Collapsing them would either lose the crisp green control or lose the teeth.

## The policies (all four proved in `banking.c` **and** instrumented on `main.c`)

| Policy | HAPPY | Context | What it proves | On `main.c`? |
|---|---|---|---|---|
| `nonrepud_complete` | **H-R** | `\postcond` | a balance changed ⇒ the audit log grew | ✅ `transfer` (default prover) |
| `nonrepud_append_only` | **H-R** | `\postcond` | old audit records are never rewritten | ✅ `transfer` (full struct → `z3 -wp-split`) |
| `bal_integrity` | **H-T** | `\writing` (`\diff(\ALL,{transfer})`) | only `transfer` may write a balance | ✅ 50/50 (`\diff` also exempts `main`, the trusted seed) |
| `authn` | **H-S** | `\precond` | `transfer` only on an authenticated session | ✅ 1/1 (call-site check in `handle_client`) |

These four cover three of the six HAPPY families (**H-T, H-R, H-S**). The remaining three — **H-I1**
(read confinement), **H-E** (privilege monotonicity), **H-I2** (noninterference) — are specified in
`../../happy-roadmap.md`, not in this directory.

**How `authn` got onto `main.c`.** H-S is an *external* check-before-use capability keyed on a session
**global** (banking.c's `session_ok`). `main.c` originally folded authentication **into** `transfer`
(it self-validates the token), so there was no global to name — and a file-level `happy \precond`
**cannot reference `transfer`'s `token` parameter** (WP rejects it: *"unbound logic variable token"*).
So a request-scoped global **`session_authenticated`** was added: `handle_client` clears it and grants
it only after validating the request's token (`get_role(token) != -1`), immediately before `transfer`
— a genuine check-before-use gate (defense in depth; `transfer` still self-validates too). The
call-site goal is **mutation-verified**: deleting the grant turns it red.

Two notes on the `main.c` instrumentation, both honest costs of *realistic* data:
- `nonrepud_append_only` is **full `AuditRecord` equality** (two `char[50]` + a `double`). That is a
  struct, so SMT splits it per field and the two 50-char array frames are heavy → it needs
  `-wp-prover z3 -wp-split` (banking.c's `int audit[]` is a scalar, so its version is trivial).
- `bal_integrity` exempts `main` alongside `transfer` because `main()` seeds the DB balances at
  startup (the trusted bootstrap); banking.c had no bootstrap, so the question didn't arise.

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

# --- main.c : all four policies on realistic, libc-using code (each shown isolated) ---
$FC -wp-prop nonrepud_complete -wp-fct transfer tests/small_example/main.c   # 1/1
$FC -wp-prop bal_integrity                      tests/small_example/main.c   # 50/50
$FC -wp-prop authn                              tests/small_example/main.c   # 1/1  (call-site in handle_client)
# full-AuditRecord append-only is struct-valued -> needs z3 + goal splitting:
frama-c -no-autoload-plugins -load-plugin wp -load-module $CMXS -macsl -wp \
        -wp-prover z3 -wp-split -wp-timeout 120 \
        -wp-prop nonrepud_append_only -wp-fct transfer tests/small_example/main.c   # 9/9
# (the headline `-wp-fct transfer` scope is 51/51 for nonrepud_complete; with the
#  full-struct append-only added it is 51/52 at the default prover and 213/213 under
#  `-wp-prover z3 -wp-split -wp-timeout 120`.)

# --- banking.c : the compliant core, all four policies green ---
$FC tests/small_example/banking.c                          # 18/18

# --- banking_attacks.c : negative controls, exactly four goals red ---
$FC tests/small_example/banking_attacks.c                  # 25/29
```

(`banking.c` / `banking_attacks.c` are also cases 24–25 in `../run.sh`. The `main.c` proof-status
detail — including the one Coq-escalable `valid_read_nstring` goal on `log_transfer`'s body — is
documented in the header of `main.c` itself.)
