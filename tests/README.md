# macsl tests

Run the Phase-0 suite (builds the plugin first):

```sh
eval $(opam env --switch=framac-coq8)
./tests/run.sh
```

Expected: `34 passed, 0 failed` (6 H-T + 3 H-I1 + 5 H-R + 3 H-E + 3 H-S + 3 H-I2 + 2 H-D + 9 worked-example).

## STRIDE coverage status (authoritative map — read this first)

Every STRIDE letter has a **shipped, prove/fail-tested** HAPPY family. This table is the single source
of truth for "what is done"; if a letter is missing or unmarked here, that is a documentation bug
(this table exists because the D row was once discoverable only inside the worked example).

| STRIDE | HAPPY | Family | `\context` | Test dir | run.sh | Status |
|---|---|---|---|---|---|---|
| **S** Spoofing | H-S | check-before-use capability | `\precond` | `phase4/` | 18–20 | shipped |
| **T** Tampering | H-T | write confinement | `\writing` + `\separated(\written,R)` | `phase0/` | 1–6 | shipped |
| **R** Repudiation | H-R | audit completeness + append-only | `\postcond` | `phase2/` | 10–14 | shipped |
| **I** Information disclosure | H-I1 / H-I2 | read confinement / noninterference | `\reading` / `\noninterference` | `phase1/`, `phase5/` | 7–9, 21–23 | shipped (H-I2 scoped: params only) |
| **D** Denial of service | H-D | totality + no-fault | `\total` (+ `-wp-rte`) | `phase6/` | 33–34 (+28–29) | shipped; flagship parser partial, `\fuel` TODO |
| **E** Elevation of privilege | H-E | privilege monotonicity | `\postcond` + `\diff` | `phase3/` | 15–17 | shipped |

Caveats are honest scope, not omissions — see `../docs/happy-roadmap.md` §4 (H-D), §7 (H-I2), §9 (gaps
GH1–GH6). Test-dir numbering = implementation milestone order (phase0=T … **phase6=D**); it is a
different axis from the roadmap §0 "macsl phase" column (see the roadmap's *Phase numbering* note).

## Why a shell runner and not ptests?

Frama-C's standard `ptests` harness runs `frama-c` with plugin autoload **on**. In this opam switch an
installed MetAcsl autoloads and declares the same ACSL builtins macsl uses (`\prop`, `\written`, …),
which clashes depending on load order. `run.sh` sidesteps that by running with
`-no-autoload-plugins` and loading only WP + macsl — the recommended way to exercise macsl standalone
(see `../docs/usage.md`). A ptests suite can be added once macsl is installed in a MetAcsl-free switch.

## Fixtures

### `phase0/` — H-T write confinement
| File | Policy | Expected |
|---|---|---|
| `writing_pos.c` | `\separated(\written, &secret)`, nothing writes `secret` | all goals proved (`4/4`) |
| `writing_neg.c` | same; `writer` writes `secret` | the `secret=42` assert unproved (`4/5`) — the **negative control** |
| `zero_targets.c` | targets a function with no write | `zero-expansion` warning |

### `phase1/` — H-I1 read confinement
| File | Policy | Expected |
|---|---|---|
| `reading_pos.c` | `\separated(\read, &secret)`, nothing reads `secret` | all goals proved (`4/4`) |
| `reading_neg.c` | same; `leak` reads `secret` | the `sink = secret` read assert unproved (`3/4`) — the **negative control** |

### `phase2/` — H-R audit-log completeness + append-only (`\postcond`)
| File | Policy | Expected |
|---|---|---|
| `audit_pos.c` | completeness; `sys_write` logs its change | `3/3` |
| `audit_neg.c` | completeness; `sys_unlink` changes `disk` without logging | completeness ensures unproved (`2/3`) |
| `immut_pos.c` | append-only; `append` writes only the new slot | `3/3` |
| `immut_neg.c` | append-only; `rewrite` overwrites `logbuf[0]` | append-only ensures unproved (`2/3`) |

### `phase3/` — H-E privilege monotonicity (`\postcond` + `\diff`)
| File | Policy | Expected |
|---|---|---|
| `priv_pos.c` | `proc_priv <= \old(proc_priv)` over `\diff(\ALL,{sudo_gate})`; non-gate fns never raise | `8/8` (gate exempt) |
| `priv_neg.c` | same; `escalate` raises privilege | monotonicity ensures unproved (`4/5`) — confused deputy |

### `phase4/` — H-S check-before-use capabilities (`\precond`)
| File | Policy | Expected |
|---|---|---|
| `authn_pos.c` | `requires session_ok==1` on `sys_write`; `handler` verifies the token first | `5/5` |
| `authn_neg.c` | same; `maintenance` calls `sys_write` directly | call-site precondition unproved (`4/5`) — forgotten check |

### `phase5/` — H-I2 noninterference via self-composition (`\noninterference`)
| File | Policy | Expected |
|---|---|---|
| `noninterf_pos.c` | `\secret(stored)` on `check`; result `== attempt` (independent of secret) | synthesized twin proves (`3/3`) |
| `noninterf_neg.c` | same; result `== attempt + stored` (leaks) | relational assert unproved (`2/3`) |

### `phase6/` — H-D denial of service (totality + no-fault, `\total`)
| File | Policy | Expected |
|---|---|---|
| `totality_pos.c` | `\context(\total)` on an always-advancing parser | terminates + no-fault, all proved (`9/9`) |
| `totality_neg.c` | same; confused parser advances only on odd `i` | `…_loop_variant_decrease` unproved (`8/9`) — the **negative control** |

### `small_example/` — worked example (all seven HAPPY families, six STRIDE letters, on one system)
| File | Role | Expected |
|---|---|---|
| `compliant.c` | compliant banking core, all four policies | `18/18` |
| `attacks.c` | four attacks, one per policy | `25/29` (four red) |
| `main.c` | the full HTTP example (now with `log_transfer`); libc is ACSL-specified, but we verify on `compliant.c` for a crisp demo | — |

See `small_example/README.md` for the policy↔attack table.

Each `*_pos.c` / `*_neg.c` is a **prove/fail pair**: the negative control going red is what makes a
green on the positive control meaningful (the non-vacuity gate — see `../docs/design.md` §4).
