# macsl

**macsl** is a Frama-C plugin that checks **HAPPY** policies — *Hyperproperty Analysis for Program
PolicY*. You state a global write-confinement property once, and macsl instruments **every matching
write site** with an ACSL `assert`, which WP discharges.

It is a standalone re-spin of CEA's [MetAcsl](https://git.frama-c.com/pub/meta) meta-property
mechanism, with one deliberate design change: macsl instruments **in place**, so

```sh
frama-c file.c -macsl -wp
```

works directly — **no `-then-last`, no file-position trap** (see [docs/design.md](docs/design.md) for
why that matters). Licence: LGPL-2.1 (inherited from MetAcsl).

## Status

Phase 0 (the `\writing` context). Builds and is verified against **Frama-C 32.1 (Germanium)**.
`./tests/run.sh` is green (6/6). The roadmap to full STRIDE coverage is in
[`happy-roadmap.md`](happy-roadmap.md); the design rationale is [`macsl-impl.md`](macsl-impl.md).

> **Honest note.** macsl was first conceived to *fix* MetAcsl, believed to be a silent no-op on
> 32.1. Running MetAcsl's own test (milestone M0) showed that was an **invocation-order mistake**, not
> a plugin bug — MetAcsl works. macsl's reason to exist is therefore the **footgun-free in-place CLI**,
> the rename to HAPPY, and the STRIDE roadmap — *not* "MetAcsl is broken." See
> [docs/design.md](docs/design.md) §1.

## Quick start

```sh
eval $(opam env --switch=framac-coq8)
dune build
# run the test suite:
./tests/run.sh
# use it on your own file (autoload disabled to avoid an installed MetAcsl
# clashing on shared ACSL builtins; see docs/usage.md):
frama-c -no-autoload-plugins -load-plugin wp \
        -load-module _build/default/src/macsl.cmxs \
        -macsl -wp -wp-rte your.c
```

## A policy

```c
int secret = 0, pub = 0;

/*@ happy \prop,
      \name("iso"),
      \targets(\ALL),
      \context(\writing),
      \separated(\written, &secret);   // no targeted function may write `secret`
*/

void f(void) { pub = 1; secret = 2; }  // the `secret = 2` assert is RED
```

See [docs/usage.md](docs/usage.md) for the full surface and options, and
[glossary/glossary.md](glossary/glossary.md) for terminology.
