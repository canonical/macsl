#!/usr/bin/env bash
# Verify the Memory.v hardening: Memory_hardened.v compiles AND every one of the
# 11 lemmas is "Closed under the global context" (no axioms, no admits).
# Usage: ./check.sh   (expects the framac-coq8 opam env active)
set -u
cd "$(dirname "$0")"
WHY3="$(why3 --print-libdir)/coq"

echo "== compile =="
coqc -R "$WHY3" Why3 Memory_hardened.v || { echo "COMPILE FAILED"; exit 1; }

LEMMAS="separated_1 separated_included separated_trans eqmem_included eqmem_sym \
havoc_access table_to_offset_zero table_to_offset_monotonic \
int_of_addr_bijection addr_of_int_bijection addr_of_null"

echo "== Print Assumptions (each must be 'Closed under the global context') =="
out="$({ echo "Require Import Memory_hardened."; for l in $LEMMAS; do echo "Print Assumptions $l."; done; } \
       | coqtop -R "$WHY3" Why3 -Q . "" 2>/dev/null)"
closed=$(grep -c 'Closed under the global context' <<<"$out")
n=$(wc -w <<<"$LEMMAS")
echo "closed: $closed / $n"
if grep -qiE 'Axioms:|admit' <<<"$out"; then echo "FAIL: axioms/admits found"; exit 1; fi
[ "$closed" -eq "$n" ] && { echo "PASS: all $n lemmas axiom-free"; exit 0; } || { echo "FAIL"; exit 1; }
