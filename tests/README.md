# macsl tests

Run the Phase-0 suite (builds the plugin first):

```sh
eval $(opam env --switch=framac-coq8)
./tests/run.sh
```

Expected: `9 passed, 0 failed` (6 Phase-0 / H-T + 3 Phase-1 / H-I1).

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

Each `*_pos.c` / `*_neg.c` is a **prove/fail pair**: the negative control going red is what makes a
green on the positive control meaningful (the non-vacuity gate — see `../docs/design.md` §4).
