#!/usr/bin/env python3
r"""
dualtp/canonical.py — the shared first-order IR + canonicalizer for the
syntactic Coq<->Lean leg (../../docs/frama-c-dual-tp-spec.md §5.4b).

This canonicalizer's ONLY job (per §5.4b) is to decide "same first-order
proposition across two prover syntaxes" — Coq and Lean. It is the TCB of leg 2
and is adversarially tested (§5.7, see corpus.py / test_canonical.py).

It parses a small but real FOL fragment that both Coq and Lean statements of the
trust-bearing coqwp lemmas land in:
  quantifiers            forall x y : T, P     /  ∀ x y : T, P
  implication (R-assoc)  P -> Q                /  P → Q
  iff                    P <-> Q               /  P ↔ Q
  conj / disj            P /\ Q , P \/ Q       /  P ∧ Q , P ∨ Q
  negation               ~P , not P            /  ¬P
  (dis)equality          a = b , a <> b        /  a = b , a ≠ b
  order                  a < b, a <= b, > , >=  /  <, ≤, >, ≥
  arithmetic             a + b, a - b, a * b, a / b
  application            f a b  or  f(a,b)
  atoms                  identifiers, integers, decimals, parens

Canonicalization makes equal exactly the things that ARE the same proposition:
  - operator SPELLINGS unified  (-> ≡ →,  /\ ≡ ∧,  <= ≡ ≤,  <> ≡ ≠, ~ ≡ ¬ ≡ not)
  - a <> b  and  ~ (a = b)  collapse to the same node
  - bound variables -> de Bruijn indices (names are irrelevant)
  - symbol/type ALIASES across provers via ALIASES below
    (Reals.Rtrigo1.PI ≡ Real.pi,  Z ≡ Int ≡ int,  R ≡ ℝ, …)
It does NOT reorder operands of any operator: a /\ b ≠ b /\ a, a -> b ≠ b -> a,
a - b ≠ b - a — so the §5.7 "swapped operand / dropped conjunct / off-by-one"
negative pairs stay UNEQUAL, as required.

Soundness direction: when in doubt, keep things DISTINCT. The canonicalizer must
never merge two different propositions (that would let a wrong Lean twin pass);
merging is restricted to the closed alias/spelling table above.
"""

import re
import sys

# ---- cross-prover symbol & type aliases (the only sanctioned merges) ----
ALIASES = {
    # types
    "Z": "INT", "int": "INT", "Int": "INT", "ℤ": "INT", "nat": "NAT", "ℕ": "NAT",
    "R": "REAL", "ℝ": "REAL", "Real": "REAL",
    "bool": "BOOL", "Bool": "BOOL", "Prop": "PROP", "addr": "ADDR", "Addr": "ADDR",
    # the pi constant (Coq Reals.Rtrigo1.PI / PI  vs  Lean Real.pi / π)
    "PI": "PI", "Reals.Rtrigo1.PI": "PI", "Rtrigo1.PI": "PI",
    "Real.pi": "PI", "pi": "PI", "π": "PI",
    # record projections / predicates shared by name across the twins
    "base": "base", "offset": "offset",
    "included": "included", "separated": "separated",
}


class Tok:
    def __init__(self, kind, val):
        self.kind = kind
        self.val = val

    def __repr__(self):
        return f"{self.kind}:{self.val}"


# multi-char / unicode operators, longest first
_OPS = [
    "<->", "↔", "->", "→", "<>", "≠", "<=", "≤", ">=", "≥", "/\\", "∧",
    "\\/", "∨", "¬", "<", ">", "=", "+", "-", "*", "/", "~", "(", ")",
    ",", ":",
]


def tokenize(s):
    toks = []
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
            continue
        # forall / ∀ , exists / ∃
        m = re.match(r"forall\b|∀|exists\b|∃", s[i:])
        if m:
            kw = m.group(0)
            toks.append(Tok("QUANT", "forall" if kw in ("forall", "∀") else "exists"))
            i += len(kw)
            continue
        m = re.match(r"not\b", s[i:])
        if m:
            toks.append(Tok("OP", "~"))
            i += 3
            continue
        matched = False
        for op in _OPS:
            if s.startswith(op, i):
                toks.append(Tok("OP", op))
                i += len(op)
                matched = True
                break
        if matched:
            continue
        # number (decimal allowed)
        m = re.match(r"\d+\.\d+|\d+", s[i:])
        if m:
            toks.append(Tok("NUM", m.group(0)))
            i += len(m.group(0))
            continue
        # identifier (dotted qualified names allowed, unicode letters)
        m = re.match(r"[^\W\d][\w'.]*", s[i:], re.UNICODE)
        if m:
            toks.append(Tok("ID", m.group(0)))
            i += len(m.group(0))
            continue
        raise SyntaxError(f"cannot tokenize at {i!r}: {s[i:i+12]!r}")
    toks.append(Tok("EOF", None))
    return toks


# operator spelling -> canonical tag
_OPCANON = {
    "<->": "iff", "↔": "iff",
    "->": "imp", "→": "imp",
    "/\\": "and", "∧": "and",
    "\\/": "or", "∨": "or",
    "<>": "ne", "≠": "ne",
    "<=": "le", "≤": "le",
    ">=": "ge", "≥": "ge",
    "<": "lt", ">": "gt", "=": "eq",
    "+": "add", "-": "sub", "*": "mul", "/": "div",
    "~": "not", "¬": "not",
}


class Parser:
    """Recursive-descent, precedence (low->high):
       forall/exists  <  <->  <  ->(R)  <  \\/  <  /\\  <  ~  <  cmp  <  +,-  <  *,/  <  app  <  atom
    """

    def __init__(self, toks):
        self.toks = toks
        self.p = 0

    def peek(self):
        return self.toks[self.p]

    def next(self):
        t = self.toks[self.p]
        self.p += 1
        return t

    def expect(self, kind, val=None):
        t = self.next()
        if t.kind != kind or (val is not None and t.val != val):
            raise SyntaxError(f"expected {kind} {val}, got {t}")
        return t

    def parse(self):
        e = self.formula()
        self.expect("EOF")
        return e

    def formula(self):
        t = self.peek()
        if t.kind == "QUANT":
            self.next()
            # binders:  x y z : T
            names = []
            while self.peek().kind == "ID":
                names.append(self.next().val)
            self.expect("OP", ":")
            ty = self.typ()
            self.expect("OP", ",")
            body = self.formula()
            # desugar multiple binders into nested quantifiers
            node = body
            for nm in reversed(names):
                node = (t.val, nm, ty, node)
            return node
        return self.iff()

    def typ(self):
        # a type is just an application-spine of ids (e.g. list Z), kept atomic-ish
        parts = [self.atom_type()]
        while self.peek().kind == "ID":
            parts.append(self.atom_type())
        if len(parts) == 1:
            return parts[0]
        return ("tyapp",) + tuple(parts)

    def atom_type(self):
        t = self.next()
        if t.kind == "ID":
            return ("ty", ALIASES.get(t.val, t.val))
        raise SyntaxError(f"bad type token {t}")

    def iff(self):
        left = self.imp()
        if self.peek().kind == "OP" and self.peek().val in ("<->", "↔"):
            self.next()
            right = self.iff()
            return ("iff", left, right)
        return left

    def imp(self):
        left = self.disj()
        if self.peek().kind == "OP" and self.peek().val in ("->", "→"):
            self.next()
            right = self.imp()  # right associative
            return ("imp", left, right)
        return left

    def disj(self):
        left = self.conj()
        while self.peek().kind == "OP" and self.peek().val in ("\\/", "∨"):
            self.next()
            right = self.conj()
            left = ("or", left, right)
        return left

    def conj(self):
        left = self.neg()
        while self.peek().kind == "OP" and self.peek().val in ("/\\", "∧"):
            self.next()
            right = self.neg()
            left = ("and", left, right)
        return left

    def neg(self):
        if self.peek().kind == "OP" and self.peek().val in ("~", "¬"):
            self.next()
            return ("not", self.neg())
        return self.cmp()

    def cmp(self):
        left = self.add()
        t = self.peek()
        if t.kind == "OP" and t.val in ("=", "<>", "≠", "<", "<=", "≤", ">", ">=", "≥"):
            self.next()
            right = self.add()
            tag = _OPCANON[t.val]
            if tag == "ne":   # a <> b  ==  ~ (a = b)
                return ("not", ("eq", left, right))
            return (tag, left, right)
        return left

    def add(self):
        left = self.mul()
        while self.peek().kind == "OP" and self.peek().val in ("+", "-"):
            op = self.next().val
            right = self.mul()
            left = (_OPCANON[op], left, right)
        return left

    def mul(self):
        left = self.app()
        while self.peek().kind == "OP" and self.peek().val in ("*", "/"):
            op = self.next().val
            right = self.app()
            left = (_OPCANON[op], left, right)
        return left

    def app(self):
        head = self.atom()
        args = []
        # f(a,b)  or  f a b
        if self.peek().kind == "OP" and self.peek().val == "(":
            # could be a parenthesised call list ONLY if head is an applicable id
            if head[0] == "id":
                self.next()
                if not (self.peek().kind == "OP" and self.peek().val == ")"):
                    args.append(self.formula())
                    while self.peek().kind == "OP" and self.peek().val == ",":
                        self.next()
                        args.append(self.formula())
                self.expect("OP", ")")
                return ("app", head) + tuple(args)
        while True:
            t = self.peek()
            if t.kind in ("ID", "NUM") or (t.kind == "OP" and t.val == "("):
                args.append(self.atom())
            else:
                break
        if args:
            return ("app", head) + tuple(args)
        return head

    def atom(self):
        t = self.peek()
        if t.kind == "OP" and t.val == "(":
            self.next()
            e = self.formula()
            self.expect("OP", ")")
            return e
        if t.kind == "ID":
            self.next()
            return ("id", ALIASES.get(t.val, t.val))
        if t.kind == "NUM":
            self.next()
            return ("num", normalize_num(t.val))
        raise SyntaxError(f"unexpected token {t}")


def normalize_num(s):
    """Canonical numeric value: keep integers as-is; decimals as exact rationals
    so 3.14 and 3.140 compare equal but 3.14 and 3.15 do not."""
    if "." in s:
        intp, frac = s.split(".")
        frac = frac.rstrip("0")
        num = int(intp + frac) if frac else int(intp)
        den = 10 ** len(frac)
        from math import gcd
        g = gcd(num, den) or 1
        return f"rat({num//g}/{den//g})"
    return f"int({int(s)})"


def _debruijn(node, env):
    """Replace bound-variable ids with de Bruijn indices; free ids stay named."""
    tag = node[0]
    if tag in ("forall", "exists"):
        _, name, ty, body = node
        return (tag, _debruijn(ty, env), _debruijn(body, [name] + env))
    if tag == "id":
        name = node[1]
        if name in env:
            return ("bvar", env.index(name))
        return node
    if tag in ("ty", "num", "bvar"):
        return node
    return (tag,) + tuple(_debruijn(c, env) for c in node[1:])


def to_ir(text):
    return Parser(tokenize(text)).parse()


def canon(text):
    """Canonical string form. canon(a)==canon(b)  iff  a,b are the same FOL prop
    (up to spelling/alias/bound-var-renaming, NOT up to operand reordering)."""
    return _sexp(_debruijn(to_ir(text), []))


def _sexp(node):
    if not isinstance(node, tuple):
        return str(node)
    return "(" + " ".join(_sexp(c) for c in node) + ")"


if __name__ == "__main__":
    # canonical.py "<stmt>"   prints the canonical form
    print(canon(sys.argv[1]))
