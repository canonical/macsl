# Mbed TLS 4.1.0 — EBIOS ↔ verification coverage gaps + Tier-3 HAPPY policies

Joins [`mbedtls-ebios-report.md`](mbedtls-ebios-report.md) (code-blind EBIOS RM, the
exogenous risk bound) to what the Frama-C/WP campaign actually covers
([`mbedtls-found-issues.md`](mbedtls-found-issues.md)), and records, per feared event:
the coverage tier, the HAPPY (MAcsl) policy where the risk is *logic* not RTE, and the
residual where it is BLOCKED. **No-blend:** a WP `PROVED` retires one *RTE/memory-safety*
class of one attack step on the amenable surface; it does not lower the EBIOS risk level —
that is the risk owner's W5 call.

## Coverage by feared event (ranking key = EBIOS severity × likelihood)

| FE (sev) | EBIOS scenario (SA) | Coverage tier | Status |
|---|---|---|---|
| **FE1** G4 — RCE/memory corruption from hostile input | SS1 / SA1 parser | **Tier-1 RTE** | raw baseline proved-in-part, **0 refuted goals**; full closure = overlay buffer contracts (asn1 leaf is the 109/109 template) |
| **FE6** G3 — DoS by remote input (memory-safety step) | SS9 / SA3,SA4 | **Tier-2 RTE** | record-length/parse over-read path amenable; resource-exhaustion *logic* BLOCKED |
| **FE2** G4 — impostor accepted (trust decision) | SS2 / SA2 validator | **Tier-3 HAPPY** | `verdict_integrity` (H-T) + `accept_checked` (H-S) — **GREEN** (driver `tier3_compliant.c`); in-situ path-validation proof on `x509_crt.c` BLOCKED (crypto + context-bloat) |
| **FE5** G3 — integrity injection / replay | SS8 / SA4,SA7 | **Tier-3 HAPPY** | `seqno_monotonic` (H-R/H-E anti-replay) — **GREEN** (driver) |
| **FE4** G4 — key/secret extraction (resumption half) | SS11 / SA7 | **Tier-3 HAPPY** | `resumption_conf` (H-I1) — **GREEN** (driver); the key-math/side-channel half is BLOCKED |
| **FE1/FE6** via state confusion | SS5 / SA3 state machine | **Tier-3 HAPPY** | `hs_sequence` (H-S) — **GREEN** (driver) |
| **FE3** G4 — channel confidentiality broken | SS3,SS4 / SA4,SA8 | **BLOCKED** | downstream of downgrade (FE7) / oracle (FE9); AEAD crypto out of reach — residual |
| **FE7** G3 — silent downgrade | SS3 / SA8 negotiation | **BLOCKED** | negotiation-policy logic; not RTE — residual |
| **FE8** G3 — forward-secrecy loss | SS10 / SA8,SA9 | **BLOCKED** | ephemeral-KEX negotiation + key math — residual |
| **FE9** G3 — secret-dependent timing/error oracle | SS4,SS7 / SA4,SA9 | **BLOCKED** | constant-time / side-channel is not a WP-RTE property — residual |
| **FE10** G4 — predictable/low-entropy RNG | SS6 / SA5 RNG | **BLOCKED** | entropy *quality* is not a WP property — residual |

Coverage summary: of 10 feared events, **2** have RTE coverage (FE1, FE6-mem-step), **4** are
**discharged GREEN** as Tier-3 HAPPY hyperproperties (FE2, FE5, FE4-resumption, FE1/FE6-state —
`tier3_compliant.c` 41/41, with red controls in `tier3_attacks.c`), and **5** are BLOCKED
residuals (FE3, FE7, FE8, FE9, FE10) — the classic crypto/entropy/negotiation/side-channel
surface that no source-level RTE/functional tool reaches.

## Tier-3 HAPPY (MAcsl) policies

Authored in [`mbedtls-acsl/patches/happy-tier3.acsl`](../../mbedtls-acsl/patches/happy-tier3.acsl).
Each states an EBIOS-feared *logic* invariant as a macsl `happy \prop` hyperproperty; because a
file-level policy cannot name a function parameter (WP: *unbound logic variable* — the
documented macsl gotcha), each verdict/state is modelled as a **request-scoped global**, exactly
the `small_example` `session_authenticated` device.

| Policy | HAPPY family (STRIDE) | EBIOS target | Discharge status |
|---|---|---|---|
| `verdict_integrity` | `\context(\writing)` H-T (T) | FE2 — only the verify routine writes the accept/reject verdict | **GREEN** (driver) + RED `tamper_verdict` |
| `accept_checked` | `\context(\precond)` H-S (S) | FE2 — `accept` only after the full chain-check gate ran | **GREEN** (driver) + RED `unchecked_accept` |
| `hs_sequence` | `\context(\precond)` H-S (S) | FE1/FE6 — protected transition only from a live/expected state | **GREEN** (driver) + RED `confused_state` |
| `resumption_conf` | `\context(\reading)` H-I1 (I) | FE4 — resumption secret never read outside the ticket/key path | **GREEN** (driver) + RED `leak_resumption` |
| `seqno_monotonic` | `\context(\postcond)` H-R/H-E (R/E) | FE5 — record seqno never decreases (anti-replay) | **GREEN** (driver) + RED `accept_record` rollback |

**Discharge (done).** All five are now **machine-checked GREEN** by macsl + WP on the focused
compliant core [`mbedtls-acsl/tier3_compliant.c`](../../mbedtls-acsl/tier3_compliant.c) — **41/41**
goals (the 5 policies = 19 instrumented assertions, + RTE), Alt-Ergo 2.6.3 / Z3 4.13.3 on
`framac-coq8`. Non-vacuity is shown by the matching red controls in
[`mbedtls-acsl/tier3_attacks.c`](../../mbedtls-acsl/tier3_attacks.c): exactly **5** goals unproved,
one per policy, each a by-construction violation (tamper write, ungated accept, confused-state
transition, secret read, seqno rollback).

This is the `small_example` driver-proof pattern (FE2/FE10): the load-bearing logic *invariant*
is discharged on a clean core where WP composes, because the real Mbed TLS units context-bloat
(`x509_crt.c` verify) or route into the BLOCKED crypto layer. **ASSUMPTION:** the invariant is
modelled with request-scoped globals (a file-level `happy \prop` cannot name a function
parameter — the documented macsl limitation), so "green" certifies the *policy logic*, not yet
its in-situ instrumentation on the real `x509_crt.c`/`ssl_tls*.c` (threading the globals into
those units, against their crypto/context-bloat residue, is the remaining in-situ step).

Run:
```
frama-c -no-autoload-plugins -load-plugin wp -load-module macsl/_build/default/src/macsl.cmxs \
        -macsl -wp -wp-rte -wp-prover alt-ergo,z3 mbedtls-acsl/tier3_compliant.c   # 41/41
```

## Residual-risk register (BLOCKED — for W5 acceptance, not treatment)

`ASSUMPTION`: per the mission, these are carried as residuals rather than halting the campaign.

1. **SA6 cryptographic primitive core** (AEAD, MAC, hash, RSA, EC, signatures) — mathematical
   correctness + **constant-time** behaviour are out of WP-RTE/functional reach. Residual:
   FE3, FE4, FE9. Mitigation outside scope: vetted constant-time implementations, test vectors.
2. **SA5 RNG / entropy** — entropy *quality/unpredictability* is not a software-safety property
   (FE10). Residual: trust the platform DRBG/entropy source.
3. **SA9 key-exchange / signature side-channels** (FE9, FE4) — timing/error oracles; residual.
4. **SA8 negotiation / downgrade & renegotiation logic** (FE7, FE8) — protocol-policy logic,
   not RTE; residual (candidate for future HAPPY policies).
5. **Supply chain / build integrity** — out of the library's software discipline entirely
   (baseline in the EBIOS report); residual.

## EBIOS W5 — sign-off **PENDING**

The verification verdicts above feed EBIOS Workshop 5 (likelihood re-rating + residual
acceptance). Per the no-blend rule the likelihood deltas are **proposed, not applied**, and the
residual register is **not accepted** until signed. **W5 sign-off is PENDING — the human risk
owner (Fabrice Derepas) has not signed.** No sign-off is fabricated.
