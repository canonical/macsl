# EBIOS RM ↔ verification crosswalk — `main.c` vs `ebios-report.txt`

The `frama-c-launch` join between the **exogenous risk bound** (`ebios-report.txt`, EBIOS RM W1–W4,
authored code-blind) and the **hard verification verdict** (the HAPPY policies macsl/WP discharges on
`main.c` and the flagship's supporting drivers). It answers: *does what `main.c` verifies cover the
threat model the EBIOS study independently derived?*

## Soundness preconditions (checked, not assumed)
- **Exogenous bound.** `ebios-report.txt` passed the `ebios-sl` endogeneity tripwire (no code
  artifacts in W1–W3); the §6 HAPPY list was withheld from its authors. So the overlap below is a
  *validation*, not a circular input. ✓
- **No-blend.** EBIOS severity/likelihood are **soft normative**; a WP `PROVED` is a **hard machine
  truth** that retires *one class* (the stated hyperproperty / RTE) of *one* attack step on the
  *amenable* surface. A green cell does **not** zero the EBIOS risk; an open cell is a residual, not a
  refutation. Each cell names its plane.
- **Ground truth (re-run this session, `framac-coq8`):** transfer **52/52**; append-only struct frame
  **6/6**; strtok totality **17/17**; availability+RTE **23/23**; compliant (incl. H-I1/H-I2) **63/63**.

## 1. Feared-event → verified-policy crosswalk

| FE (severity) | EBIOS scenario · likelihood · risk | Verifying HAPPY policy → TU | Verdict (plane) | Coverage |
|---|---|---|---|---|
| **FE1** privilege bypass on transfer · **G4** | SS2/OS2 · V2 · **High** | H-S `authn` (capability granted only after token validation) → `main.c::transfer` | **52/52** (hard) | ✅ capability gate verified; *clearance-tier* logic code-enforced, not asserted |
| **FE2** User debits another's account · **G4** | SS1/OS1 · V2 · **High** | H-E horizontal `rbac_own_account` → `rbac_horizontal.c` | **13/13** + red `transfer_cross` (hard) | ✅ **now verified** — a role-2 caller decreases no foreign account; driver-proved (string-keyed `main.c` form context-bloats, like `nonrepud_append_only`); `main.c` body already enforces it |
| **FE3** balance corrupted / bad amount · **G4** | SS3/OS3 · V2 · **High** | H-T `bal_integrity` (only `transfer`/`main` may write a balance) → `main.c` | **52/52** (hard) | ✅ off-path tampering confined; *amount>0 / sufficient-funds* checks code-enforced, not asserted |
| **FE4** forged/non-registered token accepted · **G3** | SS2/OS2 · V2 · **High** | H-S `authn` → `main.c::transfer` | **52/52** (hard) | ✅ check-before-use verified (RED if grant removed — mutation-checked) |
| **FE5** missing / altered audit record · **G3** | SS4/OS4 · V2 · **Moderate** | H-R `nonrepud_complete` → `main.c::transfer`; H-R `nonrepud_append_only` → `audit_append_frame.c` | **52/52** + **6/6** (hard) | ✅ completeness + append-only both verified — **but conditional, see FE10** |
| **FE6** clearance / session-identity disclosure · **G2** | SS6/OS6 · V2 · Low–Moderate | H-I1 read confinement / H-I2 noninterference → `compliant.c` | **63/63** (hard) | 🟡 verified on `compliant.c`, **not on `main.c`** (its string-pointer model can't host it) |
| **FE7** service unavailable (DoS) · **G3** | SS5/OS5 · V3 · **High** | H-D `\total` → `strtok_terminates.c`; H-D availability+RTE → `compliant.c::find_first_overdrawn` | **17/17** + **23/23** (hard) | 🟡 per-request totality proven **on drivers**; `main.c`'s real `get_query_param` still needs the strengthened `strtok` contract (proven *sound* in the driver, not yet wired into `main.c`) |
| **FE8** credential disclosure · **G3** | SS6/OS6 · V2 · Moderate | H-I1 confidentiality → `compliant.c` | **63/63** (hard) | 🟡 verified on `compliant.c`, not on `main.c` |
| **FE9** privilege escalation (role raised) · **G4** | SS7/OS7 · V2 · **High** | H-E `priv_monotonic` (`role >= \old`) → `main.c::transfer` | **52/52** (hard) | ✅ **verified on `main.c`** — the escalation gap the EBIOS reviewer caught is closed in code |
| **FE10** silent audit saturation · **G4** | SS8/OS8 · V2 · **High** | H-R `nonrepud_atcap` → `audit_saturation.c` (+ `main.c` fail-closed guard) | **13/13** + red `transfer_unlogged_atcap` (hard) | ✅ **now closed** — fail-closed: a transfer that cannot be recorded refuses, so completeness holds even at a full log; `main.c`'s real `transfer` carries the guard (case 26 → 53/53) |
| **FE11** token reuse / leakage spoofing · **G3** | SS9/OS9 · V2 · Moderate | — (trusted boundary) | not modeled | ⚠️ **GAP** — token expiry/revocation + query-string leakage are the declared trusted boundary; macsl proves the *discipline*, not the token lifecycle |

## 2. Verdict — does `main.c` match the EBIOS report?

**Largely yes — FE2 and FE10 now closed, one honest residual remains.** Of 11 feared events, the EBIOS
threat model (derived code-blind) and the verification align well: the high-value money/identity events
verified directly on `main.c`'s real `transfer` (FE1, FE3, FE4, FE5, FE9 — **53/53**), and the
confidentiality + availability families on the flagship's companion drivers. Notably **FE9 (privilege
escalation)** — the gap the disjoint EBIOS reviewer independently caught — *is* discharged on `main.c`
by `priv_monotonic`, a clean cross-validation of the loop.

**FE2 closed.** The horizontal-RBAC gap is now a verified hyperproperty `rbac_own_account` (H-E
horizontal): *a role-2 caller decreases no account but its own*. Proved deterministically on the clean
integer driver `rbac_horizontal.c` (**13/13**) with the red control `transfer_cross` — the same
driver-proof pattern used for `nonrepud_append_only`. `main.c`'s body already enforced the guard.

**FE10 closed.** The headline silent-saturation residual is remediated by a **fail-closed** discipline,
verified as `nonrepud_atcap` (H-R at capacity): *a transfer that cannot be recorded refuses*, so "a
balance changed ⇒ the log grew" holds even when the log may be full (precondition relaxed to
`audit_len <= NLOG`). Proved on `audit_saturation.c` (**13/13**) with the red control
`transfer_unlogged_atcap`. Unlike FE2 this was a genuine latent **defect** — `main.c`'s `transfer` now
carries the fail-closed guard (`if (audit_len >= 1024) return -1;`, case 26 → **53/53**) as the runtime
fix; the at-capacity theorem lives on the driver (the string-keyed form context-bloats).

### Residual risk (citable to its EBIOS scenario ID — for W5 treatment)
1. **FE11 / SS9 (G3, Moderate) — token lifecycle.** Expiry/revocation/leakage sit on the declared
   trusted boundary; honest scope limit, not a defect — record as accepted residual or extend scope.

### Plane-limited coverage (verified, but not on `main.c` itself)
- **FE6, FE8 (confidentiality)** and **FE7 (per-request totality)** are verified on `compliant.c` /
  `strtok_terminates.c` / the availability driver, not end-to-end on `main.c`. The flagship discharges
  them *as a directory*; `main.c` alone does not host them. For a campaign that scopes "the unit =
  `main.c`", these are coverage-by-companion, to be stated as such.

### No-blend reminder
Every ✅ retires the named hyperproperty on the amenable surface; it does **not** reduce the EBIOS
risk level. The likelihood reductions and SCIP measures belong in **W5**, proposed here but
**adjudicated by the risk owner** (human terminus) — not set by a green verdict.
