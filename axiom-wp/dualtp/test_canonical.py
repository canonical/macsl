#!/usr/bin/env python3
"""
dualtp/test_canonical.py — adversarial gate for the leg-2 canonicalizer (§5.7).

Checks, fail-closed (nonzero exit on ANY miss):
  - every POSITIVE pair canonicalizes EQUAL
  - every NEGATIVE pair canonicalizes UNEQUAL
  - idempotence: canon(canon-input) stable (re-parsing the printed IR not required;
    we check canon is a pure function — same input twice -> same output)
  - round-trip stability: canon(s) == canon(s) and parsing never crashes
  - the suite has >= 20 positive and >= 20 negative pairs (the §5.7 floor)
  - a deliberately weakened canonicalizer turns the suite RED (meta-check)
"""
import sys

from canonical import canon, to_ir, _sexp, _debruijn
from corpus import POSITIVE, NEGATIVE


def run(report=True):
    fails = []
    # floor on corpus size
    if len(POSITIVE) < 20:
        fails.append(f"POSITIVE corpus too small: {len(POSITIVE)} < 20")
    if len(NEGATIVE) < 20:
        fails.append(f"NEGATIVE corpus too small: {len(NEGATIVE)} < 20")

    for i, (a, b) in enumerate(POSITIVE):
        try:
            ca, cb = canon(a), canon(b)
        except Exception as e:
            fails.append(f"POS[{i}] parse error: {e}\n   A={a}\n   B={b}")
            continue
        if ca != cb:
            fails.append(f"POS[{i}] should be EQUAL but differ:\n   A={a}\n    -> {ca}\n   B={b}\n    -> {cb}")
        # idempotence: canon is a pure deterministic function
        if canon(a) != ca:
            fails.append(f"POS[{i}] canon not deterministic on A")

    for i, (a, b) in enumerate(NEGATIVE):
        try:
            ca, cb = canon(a), canon(b)
        except Exception as e:
            fails.append(f"NEG[{i}] parse error: {e}\n   A={a}\n   B={b}")
            continue
        if ca == cb:
            fails.append(f"NEG[{i}] should be UNEQUAL but match:\n   A={a}\n   B={b}\n   both -> {ca}")

    if report:
        print(f"corpus: {len(POSITIVE)} positive, {len(NEGATIVE)} negative pairs")
        if fails:
            print(f"FAIL ({len(fails)}):")
            for f in fails:
                print("  - " + f)
        else:
            print("ALL OK (positive equal, negative unequal, sizes >= 20)")
    return fails


def meta_weakened():
    """A weakened canonicalizer (ignore operand order of '-' and '<') MUST turn the
    suite red — proves the corpus actually discriminates (§5.7)."""
    import canonical as C
    orig = C._sexp

    def commutative_sexp(node):
        if isinstance(node, tuple) and node and node[0] in ("sub", "lt") and len(node) == 3:
            kids = sorted([C._sexp(node[1]), C._sexp(node[2])])
            return "(" + node[0] + " " + " ".join(kids) + ")"
        if isinstance(node, tuple):
            return "(" + " ".join(commutative_sexp(c) for c in node) + ")"
        return str(node)

    def weak_canon(text):
        return commutative_sexp(_debruijn(to_ir(text), []))

    saved = C.canon
    C.canon = weak_canon
    import corpus
    # re-import canon binding in this module
    global canon
    canon_saved = canon
    canon = weak_canon
    try:
        fails = run(report=False)
    finally:
        canon = canon_saved
        C.canon = saved
    return len(fails) > 0


if __name__ == "__main__":
    fails = run()
    if not meta_weakened():
        print("META-FAIL: a weakened canonicalizer did NOT turn the suite red "
              "(corpus is not discriminating enough)")
        fails = fails + ["meta"]
    sys.exit(1 if fails else 0)
