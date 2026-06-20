# macsl tests

Run the Phase-0 suite (builds the plugin first):

```sh
eval $(opam env --switch=framac-coq8)
./tests/run.sh
```

Expected: `25 passed, 0 failed` (6 H-T + 3 H-I1 + 5 H-R + 3 H-E + 3 H-S + 3 H-I2 + 2 worked-example).

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

### `small_example/` — worked example (H-R + H-S + H-T on one system)
| File | Role | Expected |
|---|---|---|
| `compliant.c` | compliant banking core, all four policies | `18/18` |
| `attacks.c` | four attacks, one per policy | `25/29` (four red) |
| `main.c` | the full HTTP example (now with `log_transfer`); libc is ACSL-specified, but we verify on `compliant.c` for a crisp demo | — |

See `small_example/README.md` for the policy↔attack table.

Each `*_pos.c` / `*_neg.c` is a **prove/fail pair**: the negative control going red is what makes a
green on the positive control meaningful (the non-vacuity gate — see `../docs/design.md` §4).
