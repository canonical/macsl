# small_example — the HAPPY/STRIDE example target

A banking-style backend (authenticate / transfer / audit over a small HTTP layer) and the
HAPPY policies that secure it. It is the main worked example for `macsl`: it shows security
policies (1) attached to realistic libc-using code, (2) proved on a compliant core, and
(3) caught going red on deliberate violations, across all seven HAPPY families
(H-T, H-R, H-S, H-E, H-I1, H-I2, H-D), i.e. the six STRIDE letters S/T/R/I/D/E. Those three
jobs are split across three `.c` files on purpose; each is needed and none is redundant.

The verdicts below are what carry trust: every policy result is discharged by Frama-C/WP
and re-checkable by re-running the proofs (see [Run](#run)). The accompanying EBIOS RM risk
study ([`ebios-report.txt`](ebios-report.txt), conformance report
[`ebios-crosswalk.md`](ebios-crosswalk.md)) was developed from the system's mission and
specification independently of the source, so the threat model is not shaped by the code it
assesses, and was reviewed and signed off by a human risk owner.

Comparing the study against the verification surfaced three gaps:

- FE10 silent audit saturation (G4, High). `nonrepud_complete` is proved only under
  `requires 0 <= audit_len < 1024`. The feared case (log full, transfers still succeeding
  unlogged) is outside the proved envelope; the precondition assumes it away.
- FE2 horizontal RBAC (G4, High). "A user may debit only their own account" is enforced in
  `transfer`'s body but was not asserted as a HAPPY hyperproperty: code-enforced, not
  machine-verified.
- FE11 token lifecycle (G3, Moderate). Expiry, revocation, and query-string leakage are the
  declared trusted boundary: a scope limit, not a defect.

FE2 was closed by a new HAPPY policy asserting the horizontal-RBAC rule (a role-2 caller may
debit only their own account) as a WP-discharged hyperproperty, with the matching attack
RED; see [rbac_horizontal.c](rbac_horizontal.c).

FE10 was closed by making the audit discipline fail-closed: a transfer that cannot record
itself must refuse, so non-repudiation (a balance changed implies the log grew) holds even
at capacity. `main.c`'s `transfer` now carries the fail-closed guard (a runtime fix for an
actual latent defect; unlike FE2, the code did not previously enforce it), and the
at-capacity theorem is proved on [audit_saturation.c](audit_saturation.c), with the
silent-saturation attack RED.

FE11 is half closed and half remains a trusted assumption. (a) Token unguessability and the
expiry clock are irreducibly the trusted boundary (spec §6); macsl does not prove a mock
token is unguessable. (b) The lifecycle discipline (a revoked, expired, or replayed token
must not authorize an operation) is check-before-use, now the verified policy `token_live`:
a protected op runs only against a currently-valid token, proved on
[token_lifecycle.c](token_lifecycle.c) with the replay attack RED. (`main.c`'s `authn`
already binds its capability to live validity via the `get_role(token) != -1` request-time
lookup.) The (a) half remains the accepted residual that the risk owner signs.


## The three files and their roles

| File | Role | What it is | `macsl -wp` result |
|---|---|---|---|
| **`main.c`** | **Realistic integration** | A full HTTP server (three routes) using real libc — `strtok`/`strcmp`/`strncpy`, `read`/`write`, `socket`/`accept`, variadic `snprintf`/`sscanf` — carrying the audit log + `log_transfer`. **Five policies are instrumented here on the real code** — the four banking ones (H-R `nonrepud_complete`, H-R `nonrepud_append_only`, H-T `bal_integrity`, H-S `authn`) plus **H-E `priv_monotonic`**. | `nonrepud_complete` **1/1** on `transfer`; `bal_integrity` **50/50** across the non-exempt functions; `authn` **1/1** (call-site check in `handle_client`); `priv_monotonic` **1/1** on `transfer`. `nonrepud_append_only` (full `AuditRecord` equality) is **context-bloated** on this big function, so its frame is proved **deterministically on an isolated driver** (`audit_append_frame.c`, see note). The *whole file* isn't all-green (the routes need loop invariants + libc specs) — which is exactly why `compliant.c` exists. |
| **`compliant.c`** | **Compliant core (the positive proof)** | A focused, fully-contracted distillation of `main.c`'s security-relevant core (accounts, audit log, `authenticate`, `log_transfer`, `transfer`, a confidential `pin`, a `check` verifier, and a bounded request handler) carrying **seven policies across six families** (H-R ×2, H-S, H-T, H-I1, H-I2, H-D). The unambiguous "every policy holds" artifact. | **63/63** — all green. |
| `attacks.c` | Negative controls | Eleven attacks, one per policy (including the two H-E forms `escalate`/`transfer_cross`, FE10 `transfer_unlogged_atcap`, and FE11 `replay_endpoint`), each violating exactly one and nothing else. Shows the policies are non-vacuous: a green that cannot go red proves nothing. | 70/81, with exactly eleven goals red, one per attack. |

Why three files, not one: `main.c` answers whether the policies attach to real-world code (they
do; the libc layer is not out of WP's reach). `compliant.c` answers whether the policies hold, on
a core small enough to be fully green and unambiguous. `attacks.c` answers whether the policies are
non-vacuous, a question that has no home in `main.c` (the compliant backend contains no violations by
design). `compliant.c` and `attacks.c` are a matched compliant/attack pair (same `#define`s, same
policy text); the contrast between all-green compliant code and the targeted reds is the assurance
argument. Collapsing them would lose either the green control or the negative controls. (H-E is the
one policy whose compliant proof lives on `main.c` rather than `compliant.c`; its attack `escalate`
still sits with the other negative controls.)

## The policies

| Policy | HAPPY | Context | What it proves | Compliant proof | Attack |
|---|---|---|---|---|---|
| `nonrepud_complete` | **H-R** | `\postcond` | a balance changed ⇒ the audit log grew | `compliant.c` + `main.c` (default) | `transfer_silent` |
| `nonrepud_atcap` | **H-R** | `\postcond` | non-repudiation holds **even at capacity** — a full log ⇒ no silent unlogged transfer (FE10, fail-closed) | `audit_saturation.c` (13/13, **deterministic driver**); `main.c` body fail-closed | `transfer_unlogged_atcap` |
| `nonrepud_append_only` | **H-R** | `\postcond` | old audit records are never rewritten | `compliant.c` (scalar) + `audit_append_frame.c` (struct, **deterministic**) | `rewrite_audit` |
| `bal_integrity` | **H-T** | `\writing` (`\diff(\ALL,{transfer})`) | only `transfer` may write a balance | `compliant.c` + `main.c` (50/50; `\diff` also exempts `main`, the trusted seed) | `tamper` |
| `authn` | **H-S** | `\precond` | `transfer` only on an authenticated session | `compliant.c` + `main.c` (call-site check in `handle_client`) | `unauth_endpoint` |
| `token_live` | **H-S** | `\precond` | an op runs only against a **currently-valid** token — no replay of a revoked/expired one (FE11 discipline) | `token_lifecycle.c` (8/8, **deterministic driver**) | `replay_endpoint` |
| `priv_monotonic` | **H-E** (vertical) | `\postcond` | a transfer never raises anyone's privilege (no tier escalation) | `main.c` `transfer` (1/1) | `escalate` |
| `rbac_own_account` | **H-E** (horizontal) | `\postcond` | a role-2 (User) caller debits no account but their own (FE2) | `rbac_horizontal.c` (13/13, **deterministic driver**) | `transfer_cross` |
| `pin_confidential` | **H-I1** | `\reading` | no code reads a confidential PIN | `compliant.c` (`\separated(\read, pin)`) | `leak_pin` |
| `noleak` | **H-I2** | `\noninterference` | `check`'s public result is independent of the secret | `compliant.c` (self-composition) | `check` (leak) |
| `availability` | **H-D** | `\total` | the request handler always returns (terminates) and faults on no input | `compliant.c` `find_first_overdrawn` (+`-wp-rte`) | `parse_request` |

These eleven policy instances cover **all seven** HAPPY families (**H-T, H-R, H-S, H-E, H-I1, H-I2,
H-D**) — the full six STRIDE letters (S/T/R/I/D/E). Three families now carry multiple forms, each closing
an EBIOS crosswalk gap: **H-R** — completeness (`nonrepud_complete`), append-only
(`nonrepud_append_only`), at-capacity (`nonrepud_atcap`, FE10); **H-S** — check-before-use (`authn`) and
token-lifecycle (`token_live`, FE11 discipline); **H-E** — *vertical* (`priv_monotonic`) and *horizontal*
(`rbac_own_account`, FE2). No family is left to `../../docs/happy-roadmap.md` only.

**On `availability` (H-D).** `\context(\total)` adds a `terminates` clause WP must discharge from the
function's `loop variant`(s); bundled with `-wp-rte` it is the "never hangs, never crashes" theorem over
*every* input. The DoS attack `parse_request` (a crafted `len` driving a loop that fails to make progress)
leaves its variant-decrease goal **red**. Scope (roadmap GH2): this bounds **WP-modelled loops** — not
wall-clock, `malloc`, or OS/socket behaviour. `main.c`'s server accept-loop is **intentionally** infinite
and carries `terminates \false;` (out of H-D scope by design).

**The `strtok` parse-loop gap — found and fixed (`strtok_terminates.c`).** H-D on `main.c`'s real
`get_query_param` does not discharge against Frama-C's *shipped* `strtok` contract: it ensures the saved
pointer stays valid/same-base but **not that it strictly advances**, so the `while (token != NULL)` loop
has no provable variant (a *proof* limitation, not a DoS bug). `strtok_terminates.c` resolves it: adding
two **sound** `ensures` (advance-while-room; a non-NULL token ⇒ room remained — both true of real strtok)
makes `\total` prove the parse loop terminates (**17/17**, run.sh case 29). To finish the *real*
`get_query_param`, those two `ensures` belong on the libc `strtok` contract (libc-side measure
`\offset(__fc_strtok_ptr)`) — a faithful upstream strengthening; until then the proof-of-fix lives in the
isolated harness, exactly the `audit_append_frame.c` pattern.

**On `priv_monotonic` (H-E).** Roles are `0`=super-admin … `2`=user, so a *smaller* number is *more*
privilege and "no escalation" is the monotonicity law `role >= \old(role)`. It is scoped to `transfer`
(the RBAC-guarded money op) where it proves cleanly; the roadmap's stronger **API-spanning** form
`\diff(\ALL,{main})` is SMT-incomplete on `main.c`'s libc-heavy routes (the trivial role-preservation
goal drowns in `strtok`/`strcmp` context — timeout, not a refutation). Its compliant proof lives on
`main.c` (compliant.c carries no role field); the confused-deputy attack `escalate` is its negative control.

**On `rbac_own_account` (H-E horizontal — the FE2 closure).** The EBIOS crosswalk flagged FE2: "a
role-2 (User) caller may debit only their own account" is *enforced* in `main.c`'s `transfer` body (the
`role==2 && from!=caller` guard) but was never *stated* as a hyperproperty. It is the **horizontal**
companion to `priv_monotonic`'s vertical law: no caller acts outside its own peer scope. As with
`authn`, a file-level policy cannot name `transfer`'s `caller` **parameter** (WP: *"unbound logic
variable"*), so the caller is modelled as a request-scoped **global capability** `caller_acct` (the same
device as `session_authenticated`). The law, stated unconditionally over globals — `role[caller_acct]==2
==> \forall a != caller_acct: balance[a] >= \old(balance[a])` — proves cleanly on the integer model
(`rbac_horizontal.c`, **13/13**, run case 30). On `main.c`'s string-keyed `transfer` the same
postcondition **context-bloats** (the caller-lookup loop + libc `strcmp`/`strlen` inflate every goal),
exactly the documented `nonrepud_append_only` cost — so the load-bearing fact is proved on the clean
driver and the cross-account attack `transfer_cross` is its red control (case 25). `main.c`'s executable
C is unchanged (the body already enforces it).

**On `nonrepud_atcap` (H-R at capacity — the FE10 closure).** The EBIOS crosswalk flagged FE10 as the
headline residual: `nonrepud_complete` is proved only under `requires 0 <= audit_len < 1024`, so the
*full-log* case — where a transfer moves money but `log_transfer` can no longer append — is **assumed
away**, a silent non-repudiation hole. Unlike FE2 (where the body already enforced the rule), this was a
genuine latent **defect**: `main.c`'s `transfer` did *not* fail-closed. The fix is the **fail-closed**
discipline — refuse a transfer that cannot be recorded — so "a balance changed ⇒ the log grew" holds
*even when the log may be full* (precondition relaxed to `audit_len <= NLOG`). It is proved on
`audit_saturation.c` (**13/13**, run case 31, deterministic), with the silent-saturation attack
`transfer_unlogged_atcap` (moves money, records only if room) as its red control (case 25).
`main.c`'s real `transfer` now carries the fail-closed guard (`if (audit_len >= 1024) return -1;`,
case 26 → **53/53**) as the runtime remediation; its verified policies keep the in-scope `audit_len <
1024` precondition, but the code no longer silently succeeds unlogged if that bound is ever reached.

**On `token_live` (H-S token lifecycle — the FE11 discipline closure).** FE11 (stale/leaked token replay)
splits into a part macsl can close and a part it cannot. **Trusted boundary (stays residual):** token
*unguessability* and the wall-clock *expiry* timer are the cryptographic primitive (spec §6) — macsl does
not prove a mock token is unguessable. **Discipline (closed):** a revoked/expired/replayed token must not
*authorize* an operation — a check-before-use property. `token_live` sharpens `authn` from "a session
exists" to "the session rests on a token valid **now**": the op is reachable only with `token_active == 1`
at the gate (proved on `token_lifecycle.c`, **8/8**, run case 32; the no-liveness-check `replay_endpoint`
is its red, case 25). `main.c` needs no new code — its `authn` already binds the capability to live
validity (`handle_client` grants only after `get_role(token) != -1`, a request-time lookup; revoking a
token by clearing `db[i].token` makes that fail and denies the capability). The unguessability/expiry
half remains the accepted residual the **risk owner** signs (the human terminus of the EBIOS loop).

**On `pin_confidential` (H-I1) and `noleak` (H-I2) — why on `compliant.c`, not `main.c`.** These two
confidentiality families need shapes `main.c`'s realistic code does not provide cleanly: H-I1's
`\separated(\read, secret)` is provable only when the read locations are *named* and distinct from the
secret — `main.c`'s string routines read arbitrary `char*` parameters whose separation from the
secret bytes is unknown without extra preconditions (and char-vs-char defeats the chunk-typing that
made `bal_integrity` free). H-I2's self-composition needs a function with a **secret parameter** and a
**functional `ensures`**; `main.c`'s `authenticate` deliberately makes its result *depend* on the
secret (token-based), so it is not noninterference-clean. Both are therefore demonstrated on the
synthetic core, mirroring the verified `tests/phase1` / `tests/phase5` controls.

**How `authn` got onto `main.c`.** H-S is an *external* check-before-use capability keyed on a session
**global** (compliant.c's `session_ok`). `main.c` originally folded authentication **into** `transfer`
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
  policy. (`compliant.c` proves the same policy on a scalar log; the driver covers the struct case.)
- `bal_integrity` exempts `main` alongside `transfer` because `main()` seeds the DB balances at
  startup (the trusted bootstrap); compliant.c had no bootstrap, so the question didn't arise.

## The eleven attacks (caught in `attacks.c`)

| Attack | Violates | Caught as |
|---|---|---|
| `transfer_silent` — moves money, never logs | `nonrepud_complete` (H-R) | `transfer_silent…nonrepud_complete` red |
| `transfer_unlogged_atcap` — moves money at capacity, records only if room | `nonrepud_atcap` (H-R, FE10) | `transfer_unlogged_atcap…nonrepud_atcap` red |
| `rewrite_audit` — overwrites `audit[0]` | `nonrepud_append_only` (H-R) | `rewrite_audit…nonrepud_append_only` red |
| `tamper` — writes a balance directly | `bal_integrity` (H-T) | `tamper…bal_integrity` red |
| `unauth_endpoint` — calls `transfer` without auth | `authn` (H-S) | `unauth_endpoint_call_transfer_requires_authn` red |
| `replay_endpoint` — acts on a token without a liveness check (replay) | `token_live` (H-S, FE11) | `replay_endpoint…token_live` red |
| `escalate` — confused deputy: lowers a role (grants super-admin) | `priv_monotonic` (H-E vertical) | `escalate…priv_monotonic` red |
| `transfer_cross` — role-2 caller debits a foreign account (no own-account guard) | `rbac_own_account` (H-E horizontal, FE2) | `transfer_cross…rbac_own_account` red |
| `leak_pin` — reads a confidential PIN into a public sink | `pin_confidential` (H-I1) | `leak_pin…pin_confidential` red |
| `check` (leak) — result depends on the secret (`attempt + stored`) | `noleak` (H-I2) | `check_selfcomp…noleak` red |
| `parse_request` — crafted `len` drives a no-progress loop | `availability` (H-D) | `parse_request…terminates`/`loop variant` red |

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

# --- compliant.c : the compliant core, seven policies (six families) all green ---
$FC tests/small_example/compliant.c                          # 63/63
# H-D availability, full claim (terminates + never-faults) on the request handler:
$FC -wp-rte -wp-fct find_first_overdrawn tests/small_example/compliant.c   # all green (Terminating)

# --- attacks.c : negative controls, exactly eleven goals red ---
$FC tests/small_example/attacks.c                  # 70/81

# --- rbac_horizontal.c : FE2 horizontal access control, proved (H-E horizontal) ---
$FC tests/small_example/rbac_horizontal.c          # 13/13  (transfer_cross is its red, in attacks.c)

# --- audit_saturation.c : FE10 fail-closed non-repudiation at capacity (H-R) ---
$FC tests/small_example/audit_saturation.c         # 13/13  (transfer_unlogged_atcap is its red)

# --- token_lifecycle.c : FE11 token-lifecycle discipline, proved (H-S) ---
$FC tests/small_example/token_lifecycle.c          # 8/8    (replay_endpoint is its red, in attacks.c)
```

(`compliant.c` / `attacks.c` are also cases 24–25 in `../run.sh`. The `main.c` proof-status
detail — including the one Coq-escalable `valid_read_nstring` goal on `log_transfer`'s body — is
documented in the header of `main.c` itself.)
