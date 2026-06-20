# small_example — the flagship HAPPY/STRIDE target

A banking-style backend (authenticate / transfer / audit over a tiny HTTP layer) and the **HAPPY**
policies that secure it. This is the **flagship example** for `macsl`: it shows security policies
(1) attached to **realistic** libc-using code, (2) **proved** on a crisp compliant core, and
(3) **caught going red** on deliberate violations — across **all six HAPPY/STRIDE families**
(H-T, H-R, H-S, H-E, H-I1, H-I2). Those three jobs are split across three `.c` files on purpose —
each is load-bearing; none is redundant.

## The three files and their roles

| File | Role | What it is | `macsl -wp` result |
|---|---|---|---|
| **`main.c`** | **Realistic integration** | A full HTTP server (three routes) using real libc — `strtok`/`strcmp`/`strncpy`, `read`/`write`, `socket`/`accept`, variadic `snprintf`/`sscanf` — carrying the audit log + `log_transfer`. **Five policies are instrumented here on the real code** — the four banking ones (H-R `nonrepud_complete`, H-R `nonrepud_append_only`, H-T `bal_integrity`, H-S `authn`) plus **H-E `priv_monotonic`**. | `nonrepud_complete` **1/1** on `transfer`; `bal_integrity` **50/50** across the non-exempt functions; `authn` **1/1** (call-site check in `handle_client`); `priv_monotonic` **1/1** on `transfer`. `nonrepud_append_only` (full `AuditRecord` equality) is **context-bloated** on this big function, so its frame is proved **deterministically on an isolated driver** (`audit_append_frame.c`, see note). The *whole file* isn't all-green (the routes need loop invariants + libc specs) — which is exactly why `banking.c` exists. |
| **`banking.c`** | **Compliant core (the positive proof)** | A focused, fully-contracted distillation of `main.c`'s security-relevant core (accounts, audit log, `authenticate`, `log_transfer`, `transfer`, plus a confidential `pin` and a `check` verifier) carrying **six policies across five families** (H-R ×2, H-S, H-T, H-I1, H-I2). The unambiguous "every policy holds" artifact. | **43/43** — all green. |
| **`banking_attacks.c`** | **Negative controls (the teeth)** | **Seven attacks**, **one per policy**, each violating exactly one and nothing else. Proves the policies are **non-vacuous** — a green that cannot go red proves nothing. | **34/41** — exactly **seven** goals red, one per attack. |

**Why three, not one.** `main.c` answers *"do the policies attach to real-world code?"* (yes — the
libc layer is **not** "out of WP's reach"). `banking.c` answers *"do the policies hold?"* on a core
small enough to be **fully green and unambiguous**. `banking_attacks.c` answers *"do the policies have
teeth?"* — and that question has no home in `main.c`, which is the *compliant* backend and contains no
violations by design. `banking.c` + `banking_attacks.c` are a **matched compliant/attack pair** (same
`#define`s, same policy text); the contrast between all-green compliant code and the targeted reds is
the actual assurance argument. Collapsing them would either lose the crisp green control or lose the
teeth. (H-E is the one policy whose compliant proof lives on `main.c` rather than `banking.c` — its
attack `escalate` still sits with the other negative controls.)

## The policies

| Policy | HAPPY | Context | What it proves | Compliant proof | Attack |
|---|---|---|---|---|---|
| `nonrepud_complete` | **H-R** | `\postcond` | a balance changed ⇒ the audit log grew | `banking.c` + `main.c` (default) | `transfer_silent` |
| `nonrepud_append_only` | **H-R** | `\postcond` | old audit records are never rewritten | `banking.c` (scalar) + `audit_append_frame.c` (struct, **deterministic**) | `rewrite_audit` |
| `bal_integrity` | **H-T** | `\writing` (`\diff(\ALL,{transfer})`) | only `transfer` may write a balance | `banking.c` + `main.c` (50/50; `\diff` also exempts `main`, the trusted seed) | `tamper` |
| `authn` | **H-S** | `\precond` | `transfer` only on an authenticated session | `banking.c` + `main.c` (call-site check in `handle_client`) | `unauth_endpoint` |
| `priv_monotonic` | **H-E** | `\postcond` | a transfer never raises anyone's privilege | `main.c` `transfer` (1/1) | `escalate` |
| `pin_confidential` | **H-I1** | `\reading` | no code reads a confidential PIN | `banking.c` (`\separated(\read, pin)`) | `leak_pin` |
| `noleak` | **H-I2** | `\noninterference` | `check`'s public result is independent of the secret | `banking.c` (self-composition) | `check` (leak) |

These seven policies cover **all six** HAPPY families (**H-T, H-R, H-S, H-E, H-I1, H-I2**) — full family
coverage. No family is left to `happy-roadmap.md` only.

**On `priv_monotonic` (H-E).** Roles are `0`=super-admin … `2`=user, so a *smaller* number is *more*
privilege and "no escalation" is the monotonicity law `role >= \old(role)`. It is scoped to `transfer`
(the RBAC-guarded money op) where it proves cleanly; the roadmap's stronger **API-spanning** form
`\diff(\ALL,{main})` is SMT-incomplete on `main.c`'s libc-heavy routes (the trivial role-preservation
goal drowns in `strtok`/`strcmp` context — timeout, not a refutation). Its compliant proof lives on
`main.c` (banking.c carries no role field); the confused-deputy attack `escalate` is its negative control.

**On `pin_confidential` (H-I1) and `noleak` (H-I2) — why on `banking.c`, not `main.c`.** These two
confidentiality families need shapes `main.c`'s realistic code does not provide cleanly: H-I1's
`\separated(\read, secret)` is provable only when the read locations are *named* and distinct from the
secret — `main.c`'s string routines read arbitrary `char*` parameters whose separation from the
secret bytes is unknown without extra preconditions (and char-vs-char defeats the chunk-typing that
made `bal_integrity` free). H-I2's self-composition needs a function with a **secret parameter** and a
**functional `ensures`**; `main.c`'s `authenticate` deliberately makes its result *depend* on the
secret (token-based), so it is not noninterference-clean. Both are therefore demonstrated on the
synthetic core, mirroring the verified `tests/phase1` / `tests/phase5` controls.

**How `authn` got onto `main.c`.** H-S is an *external* check-before-use capability keyed on a session
**global** (banking.c's `session_ok`). `main.c` originally folded authentication **into** `transfer`
(it self-validates the token), so there was no global to name — and a file-level `happy \precond`
**cannot reference `transfer`'s `token` parameter** (WP rejects it: *"unbound logic variable token"*).
So a request-scoped global **`session_authenticated`** was added: `handle_client` clears it and grants
it only after validating the request's token (`get_role(token) != -1`), immediately before `transfer`
— a genuine check-before-use gate (defense in depth; `transfer` still self-validates too). The
call-site goal is **mutation-verified**: deleting the grant turns it red.

Two notes on the `main.c` instrumentation, both honest costs of *realistic* data:
- **`nonrepud_append_only` and context bloat (proved deterministically on a driver).** The policy is
  full `AuditRecord` equality (two `char[50]` + a `double`). On `main.c`'s real `transfer` that goal is
  intractable — **not because the property is hard, but because of context bloat**: transfer's
  user-lookup loop and the libc `strcmp`/`strlen` contracts are dragged into every split goal. We
  measured this carefully: SMT only closes the two `char[50]` frames by **wall-clock grinding** (~150 s,
  and the result *flips* with the prover combo and timeout), and a **deterministic** budget of
  2,000,000 steps still fails — i.e. a machine-dependent non-proof. Coq is no better: each split goal is
  a ~2660-line context-bloated VC. The rigorous remedy (the documented "isolate a driver" pattern) is
  **`audit_append_frame.c`**: a tiny driver carrying `log_transfer`'s *exact* frame contract
  (`assigns logbuf[len], len;`) and the same full-struct policy. Free of the bloat, it discharges the
  two `char[50]` frames **deterministically** under a bounded 50 000-step budget (`6/6`, run case 27) —
  a machine-independent proof, not a timeout. So the append-only property *is* proved by provers; what
  `main.c` cannot give is a *clean VC* for it, which is a property of that big function, not of the
  policy. (`banking.c` proves the same policy on a scalar log; the driver covers the struct case.)
- `bal_integrity` exempts `main` alongside `transfer` because `main()` seeds the DB balances at
  startup (the trusted bootstrap); banking.c had no bootstrap, so the question didn't arise.

## The seven attacks (caught in `banking_attacks.c`)

| Attack | Violates | Caught as |
|---|---|---|
| `transfer_silent` — moves money, never logs | `nonrepud_complete` (H-R) | `transfer_silent…nonrepud_complete` red |
| `rewrite_audit` — overwrites `audit[0]` | `nonrepud_append_only` (H-R) | `rewrite_audit…nonrepud_append_only` red |
| `tamper` — writes a balance directly | `bal_integrity` (H-T) | `tamper…bal_integrity` red |
| `unauth_endpoint` — calls `transfer` without auth | `authn` (H-S) | `unauth_endpoint_call_transfer_requires_authn` red |
| `escalate` — confused deputy: lowers a role (grants super-admin) | `priv_monotonic` (H-E) | `escalate…priv_monotonic` red |
| `leak_pin` — reads a confidential PIN into a public sink | `pin_confidential` (H-I1) | `leak_pin…pin_confidential` red |
| `check` (leak) — result depends on the secret (`attempt + stored`) | `noleak` (H-I2) | `check_selfcomp…noleak` red |

## Run

```sh
eval $(opam env --switch=framac-coq8)
dune build
CMXS=_build/default/src/macsl.cmxs
FC="frama-c -no-autoload-plugins -load-plugin wp -load-module $CMXS -macsl -wp -wp-prover alt-ergo,z3"

# --- main.c : the policies on realistic, libc-using code (each shown isolated) ---
$FC -wp-prop nonrepud_complete -wp-fct transfer tests/small_example/main.c   # 1/1
$FC -wp-prop bal_integrity                      tests/small_example/main.c   # 50/50
$FC -wp-prop authn                              tests/small_example/main.c   # 1/1  (call-site in handle_client)
$FC -wp-prop priv_monotonic -wp-fct transfer    tests/small_example/main.c   # 1/1  (H-E: transfer raises no role)
# nonrepud_append_only on main.c's transfer is context-bloated (its loop + libc
# contracts inflate the goal); the full-struct frame is proved DETERMINISTICALLY on
# an isolated driver instead -- a bounded step budget, not a wall-clock grind:
$FC -wp-split -wp-steps 50000 -wp-timeout 60 tests/small_example/audit_append_frame.c   # 6/6 (deterministic)

# --- banking.c : the compliant core, six policies (five families) all green ---
$FC tests/small_example/banking.c                          # 43/43

# --- banking_attacks.c : negative controls, exactly seven goals red ---
$FC tests/small_example/banking_attacks.c                  # 34/41
```

(`banking.c` / `banking_attacks.c` are also cases 24–25 in `../run.sh`. The `main.c` proof-status
detail — including the one Coq-escalable `valid_read_nstring` goal on `log_transfer`'s body — is
documented in the header of `main.c` itself.)
