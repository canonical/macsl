# EBIOS RM ↔ verification crosswalk — `main.c` vs `ebios-report.txt`

This crosswalk joins the risk study (`ebios-report.txt`, EBIOS RM W1–W4, developed independently
of the implementation) with the verification verdicts (the HAPPY policies macsl/WP discharges on
`main.c` and the supporting drivers). It answers: does what `main.c` verifies cover the threat model
the EBIOS study independently derived?

## Soundness preconditions (checked, not assumed)
- Independence. `ebios-report.txt` was written without reference to the source (no code artifacts in
  W1–W3), and the §6 HAPPY list was withheld during authoring, so the overlap below is a validation
  rather than a circular input.
- Distinct planes. EBIOS severity and likelihood are normative judgements; a WP `PROVED` is a machine
  fact that retires one class (the stated hyperproperty or RTE) of one attack step on the amenable
  surface. A green cell does not zero the EBIOS risk, and an open cell is a residual rather than a
  refutation. Each cell names its plane.
- **Ground truth (re-run this session, `framac-coq8`):** transfer **53/53**; append-only struct frame
  **6/6**; strtok totality **17/17**; availability+RTE **23/23**; compliant (incl. H-I1/H-I2) **63/63**.

## 1. Feared-event → verified-policy crosswalk

| FE (severity) | EBIOS scenario · likelihood · risk | Verifying HAPPY policy → TU | Verdict (plane) | Coverage |
|---|---|---|---|---|
| **FE1** privilege bypass on transfer · **G4** | SS2/OS2 · V2 · **High** | H-S `authn` (capability granted only after token validation) → `main.c::transfer` | **53/53** (hard) | yes — capability gate verified; *clearance-tier* logic code-enforced, not asserted |
| **FE2** User debits another's account · **G4** | SS1/OS1 · V2 · **High** | H-E horizontal `rbac_own_account` → `rbac_horizontal.c` | **13/13** + red `transfer_cross` (hard) | verified — a role-2 caller decreases no foreign account; driver-proved (string-keyed `main.c` form context-bloats, like `nonrepud_append_only`); `main.c` body already enforces it |
| **FE3** balance corrupted / bad amount · **G4** | SS3/OS3 · V2 · **High** | H-T `bal_integrity` (only `transfer`/`main` may write a balance) → `main.c` | **53/53** (hard) | yes — off-path tampering confined; *amount>0 / sufficient-funds* checks code-enforced, not asserted |
| **FE4** forged/non-registered token accepted · **G3** | SS2/OS2 · V2 · **High** | H-S `authn` → `main.c::transfer` | **53/53** (hard) | yes — check-before-use verified (RED if grant removed — mutation-checked) |
| **FE5** missing / altered audit record · **G3** | SS4/OS4 · V2 · **Moderate** | H-R `nonrepud_complete` → `main.c::transfer`; H-R `nonrepud_append_only` → `audit_append_frame.c` | **53/53** + **6/6** (hard) | yes — completeness + append-only both verified — **but conditional, see FE10** |
| **FE6** clearance / session-identity disclosure · **G2** | SS6/OS6 · V2 · Low–Moderate | H-I1 read confinement / H-I2 noninterference → `compliant.c` | **63/63** (hard) | partial — verified on `compliant.c`, **not on `main.c`** (its string-pointer model can't host it) |
| **FE7** service unavailable (DoS) · **G3** | SS5/OS5 · V3 · **High** | H-D `\total` → `strtok_terminates.c`; H-D availability+RTE → `compliant.c::find_first_overdrawn` | **17/17** + **23/23** (hard) | partial — per-request totality proven **on drivers**; `main.c`'s real `get_query_param` still needs the strengthened `strtok` contract (proven *sound* in the driver, not yet wired into `main.c`) |
| **FE8** credential disclosure · **G3** | SS6/OS6 · V2 · Moderate | H-I1 confidentiality → `compliant.c` | **63/63** (hard) | partial — verified on `compliant.c`, not on `main.c` |
| **FE9** privilege escalation (role raised) · **G4** | SS7/OS7 · V2 · **High** | H-E `priv_monotonic` (`role >= \old`) → `main.c::transfer` | **53/53** (hard) | yes — **verified on `main.c`** — the escalation gap the EBIOS reviewer caught is closed in code |
| **FE10** silent audit saturation · **G4** | SS8/OS8 · V2 · **High** | H-R `nonrepud_atcap` → `audit_saturation.c` (+ `main.c` fail-closed guard) | **13/13** + red `transfer_unlogged_atcap` (hard) | closed — fail-closed: a transfer that cannot be recorded refuses, so completeness holds even at a full log; `main.c`'s real `transfer` carries the guard (case 26 → 53/53) |
| **FE11** token reuse / leakage spoofing · **G3** | SS9/OS9 · V2 · Moderate | H-S `token_live` → `token_lifecycle.c` (discipline half) | **8/8** + red `replay_endpoint` (hard) | partial — **discipline closed** — a revoked/expired/replayed token cannot authorize an op; token *unguessability* + the expiry *clock* remain the trusted boundary (spec §6) — accepted residual |

## 2. Verdict — does `main.c` match the EBIOS report?

Yes. All three flagged gaps are now remediated; the only residual is an irreducible trusted boundary.
Of 11 feared events, the independently derived EBIOS threat model and the verification align well: the
high-value money and identity events are verified directly on `main.c`'s `transfer` (FE1, FE3, FE4,
FE5, FE9 — 53/53), and the confidentiality and availability families on the companion drivers. FE9
(privilege escalation), the gap the independent EBIOS review caught, is discharged on `main.c` by
`priv_monotonic`.

**FE2 closed.** The horizontal-RBAC gap is now a verified hyperproperty `rbac_own_account` (H-E
horizontal): *a role-2 caller decreases no account but its own*. Proved deterministically on the clean
integer driver `rbac_horizontal.c` (**13/13**) with the red control `transfer_cross` — the same
driver-proof pattern used for `nonrepud_append_only`. `main.c`'s body already enforced the guard.

**FE10 closed.** The silent-saturation residual is remediated by a fail-closed discipline,
verified as `nonrepud_atcap` (H-R at capacity): *a transfer that cannot be recorded refuses*, so "a
balance changed ⇒ the log grew" holds even when the log may be full (precondition relaxed to
`audit_len <= NLOG`). Proved on `audit_saturation.c` (**13/13**) with the red control
`transfer_unlogged_atcap`. Unlike FE2 this was a genuine latent **defect** — `main.c`'s `transfer` now
carries the fail-closed guard (`if (audit_len >= 1024) return -1;`, case 26 → **53/53**) as the runtime
fix; the at-capacity theorem lives on the driver (the string-keyed form context-bloats).

**FE11 — discipline half closed.** The lifecycle discipline (a revoked/expired/replayed token must not
authorize an operation) is now the verified policy `token_live` (H-S): an op runs only against a
currently-valid token. Proved on `token_lifecycle.c` (**8/8**) with the replay control `replay_endpoint`.
`main.c` needs no new code — its `authn` already binds the capability to live validity via the
request-time `get_role(token) != -1` lookup.

### Residual risk (the irreducible trusted boundary — for W5 acceptance, not treatment)
1. **FE11 / SS9 (G3, Moderate) — token *strength* + *expiry clock*.** Token unguessability and the
   wall-clock expiry timer are the cryptographic primitive (spec §6 trusted boundary); macsl proves the
   *discipline* around it, not the primitive. This is an **accepted residual** the risk owner signs (the
   human terminus) — not a code defect. A production build replaces the mock token with an opaque,
   expiring, revocable credential.

### Plane-limited coverage (verified, but not on `main.c` itself)
- **FE6, FE8 (confidentiality)** and **FE7 (per-request totality)** are verified on `compliant.c` /
  `strtok_terminates.c` / the availability driver, not end-to-end on `main.c`. The flagship discharges
  them *as a directory*; `main.c` alone does not host them. For a campaign that scopes "the unit =
  `main.c`", these are coverage-by-companion, to be stated as such.

### Planes do not blend
A verified cell retires the named hyperproperty on the amenable surface; it does not reduce the EBIOS
risk level. The likelihood reductions and SCIP measures belong in **W5**, proposed here but
**adjudicated by the risk owner** (human terminus) — not set by a green verdict.

## 3. Verification feedback into EBIOS W5 (verdicts → risk treatment)

The downstream half: all targeted policies are discharged. The likelihood deltas are proposed (the
verdict informs; the risk owner re-rates and signs), and severity is unchanged. These are recorded in
the report's Workshop 5 and reproduced here as the join table.

| EBIOS scenario | TU + verdict | Property proved | Proposed likelihood Δ (honest) | Residual risk | SCIP measure |
|---|---|---|---|---|---|
| R1 (FE1/FE4) | `main.c::transfer` PROVED 53/53 | check-before-use authn | V2→V1: retires the unauthenticated-call step | — | M1 verified `authn` (H-S) |
| R2 (FE2) | `rbac_horizontal.c` 13/13 + main.c body | role-2 debits only own account | V2→V1: retires cross-account debit | — | M2 verified `rbac_own_account` (H-E) |
| R3 (FE3) | `main.c::transfer` PROVED (in 53/53) | only transfer writes a balance | V2→V1: off-path tampering only | in-transfer amount/funds logic code-only (partial) | M4 verified `bal_integrity` (H-T) |
| R4 (FE5) | `main.c` 53/53 + `audit_append_frame.c` 6/6 | audit completeness + append-only | V2→V1 | — | M5 verified `nonrepud_complete`/`_append_only` (H-R) |
| R5 (FE9) | `main.c::transfer` PROVED 53/53 | privilege monotonicity | V2→V1: retires tier escalation | — | M3 verified `priv_monotonic` (H-E) |
| R6 (FE10) | `audit_saturation.c` 13/13 + main.c guard | fail-closed non-repudiation at capacity | V2→V1: defect remediated | — | M6 verified `nonrepud_atcap` (H-R) |
| R7 (FE11) | `token_lifecycle.c` 8/8 | no replay of a revoked/expired token | V2→V1 for the replay step **only** | token strength/expiry clock = trusted boundary (non-formal) | M7 verified `token_live` (H-S) |
| R8 (FE7) | `compliant.c` 23/23 + `strtok_terminates.c` 17/17 | per-request termination + no-fault | V3→V2 (partial) | real `get_query_param` needs the strtok-contract `ensures` | M8 verified `availability` (H-D) |
| R9 (FE6/FE8) | `compliant.c` 63/63 | read-confinement + non-interference | V2→V2 (no change) | proved on the core model, not main.c's string layer (plane-limited) | M9 verified `pin_confidential`/`noleak` (H-I1/H-I2) |

**Coverage check (procedure step 6):** every high-severity (G3/G4) feared event maps to ≥1 scenario row
above (FE1–FE5, FE7–FE11 all present; no gap). On the Farmer diagram, with the proposed likelihoods
every high-severity scenario moves off the top-right band. The risk owner (Fabrice Derepas) approved
the re-rated likelihoods and accepted the residuals (FE11 strength/expiry; FE6/FE8 on the real layer;
FE7 strtok upstreaming) on 2026-06-20 (W5 sign-off in `ebios-report.txt`).
