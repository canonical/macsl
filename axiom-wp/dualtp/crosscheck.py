#!/usr/bin/env python3
"""
dualtp/crosscheck.py — leg-2 (syntactic Coq<->Lean) cross-check driver
(../../docs/frama-c-dual-tp-spec.md §5.4b).

For each lemma in pairs.PAIRS: canonicalize the Coq statement and the Lean
statement to the shared FOL IR and require structural equality. Fail-closed:
any mismatch / parse error -> nonzero exit.

This is leg 2 of the hybrid 3-way check. Leg 1 (semantic Why3<->Coq) is the Coq
proof against the why3-semantics denotational model (axiom-wp/leg1/); a family is
fully CERTIFIED only when both legs hold for it. crosscheck.py reports the leg-2
verdict; it does not by itself claim certification.
"""
import sys

from canonical import canon
from pairs import PAIRS, OUT_OF_FRAGMENT


def run():
    rc = 0
    print(f"leg-2 Coq<->Lean cross-check: {len(PAIRS)} lemma(s)")
    for name, p in sorted(PAIRS.items()):
        try:
            cc, cl = canon(p["coq"]), canon(p["lean"])
        except Exception as e:
            print(f"  FAIL {name}: parse error: {e}")
            rc = 1
            continue
        if cc == cl:
            print(f"  OK   {name}: canon(Coq) == canon(Lean)")
        else:
            print(f"  FAIL {name}: canon differs")
            print(f"        Coq  -> {cc}")
            print(f"        Lean -> {cl}")
            rc = 1
    if OUT_OF_FRAGMENT:
        print("not yet leg-2 cross-checked (statement outside the FOL fragment, §5.8):")
        for k, why in sorted(OUT_OF_FRAGMENT.items()):
            print(f"  - {k}: {why}")
    print("CROSSCHECK OK" if rc == 0 else "CROSSCHECK FAILURES")
    return rc


if __name__ == "__main__":
    sys.exit(run())
