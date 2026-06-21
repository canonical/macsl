#!/usr/bin/env bash
# Verify the coqwp hardening files. For each file: it compiles, contains no
# Admitted/admit, and Print Assumptions on every listed lemma yields either
# "Closed under the global context" or axioms drawn ONLY from that file's
# whitelist of STANDARD Coq axioms (3rd arg, an ERE; empty = none allowed).
# Usage: ./check.sh   (expects the framac-coq8 opam env active)
set -u
cd "$(dirname "$0")"
WHY3="$(why3 --print-libdir)/coq"
rc=0

check_file () {            # <file> <allowed_axiom_ere> <lemma...>
  local file="$1" allow="$2"; shift 2
  echo "== $file =="
  # 1. no Admitted/admit in the actual proofs (each comment line starts with "(*")
  if grep -vE '^\s*\(\*' "$file" | grep -qE '(Admitted\.|\badmit\b)'; then
    echo "  FAIL: contains Admitted/admit"; rc=1; return
  fi
  # 2. compiles
  coqc -R "$WHY3" Why3 "$file" 2>/dev/null || { echo "  COMPILE FAILED"; rc=1; return; }
  local mod="${file%.v}" out closed bad
  out="$({ echo "Require Import $mod."; for l in "$@"; do echo "Print Assumptions $l."; done; } \
          | coqtop -R "$WHY3" Why3 -Q . "" 2>/dev/null)"
  closed=$(grep -c 'Closed under the global context' <<<"$out")
  # axiom-name lines are at column 0 and end in " :"; any not matching the
  # per-file whitelist is an unexpected axiom.
  if [ -z "$allow" ]; then
    bad=$(grep -cE '^[^ ].* :$' <<<"$out")
  else
    bad=$(grep -E '^[^ ].* :$' <<<"$out" | grep -cvE "$allow")
  fi
  echo "  lemmas=$# closed=$closed allowed-axioms='${allow:-none}' unexpected=$bad"
  if [ "$bad" -ne 0 ]; then
    echo "  FAIL: unexpected axiom"
    grep -E '^[^ ].* :$' <<<"$out" | { [ -n "$allow" ] && grep -vE "$allow" || cat; } | sed 's/^/    /'
    rc=1; return
  fi
  echo "  OK"
}

check_file Memory_hardened.v '' \
  separated_1 separated_included separated_trans eqmem_included eqmem_sym \
  havoc_access table_to_offset_zero table_to_offset_monotonic \
  int_of_addr_bijection addr_of_int_bijection addr_of_null

check_file Vset_hardened.v 'functional_extensionality' \
  member_bool1 member_empty member_singleton member_union member_inter \
  union_empty inter_empty member_range member_range_sup member_range_inf \
  member_range_all

# Cfloat: Coq's R is itself axiomatized, so "Closed" is unattainable; the lemmas
# may depend only on the two STANDARD axioms Coq's Reals are built on.
check_file Cfloat_hardened.v 'functional_extensionality|sig_forall_dec' \
  to_f32_zero to_f32_one to_f64_zero to_f64_one float_32 float_64 \
  is_finite_to_float_32 is_finite_to_float_64 to_float_is_finite_32 \
  to_float_is_finite_64 finite_small_f32 finite_small_f64 finite_range_f32 \
  finite_range_f64 eq_finite_f32 eq_finite_f64 ne_finite_f32 ne_finite_f64 \
  le_finite_f32 le_finite_f64 lt_finite_f32 lt_finite_f64 neg_finite_f32 \
  neg_finite_f64 add_finite_f32 add_finite_f64 mul_finite_f32 mul_finite_f64 \
  div_finite_f32 div_finite_f64 sqrt_finite_f32 sqrt_finite_f64

# ArcTrigo / ExpLog: genuine realizations over Coq's own asin/acos/exp; same
# standard-Reals-axiom footing as Cfloat.
check_file ArcTrigo_hardened.v 'functional_extensionality|sig_forall_dec' \
  Sin_asin Cos_acos

check_file ExpLog_hardened.v 'functional_extensionality|sig_forall_dec' \
  exp_pos

# Trigonometry: Pi_double_precision_bounds via CoqInterval. All-standard footprint:
# classical logic (Classical_Prop.classic, ClassicalDedekindReals.sig_*), functional
# extensionality, and Coq native 63-bit integer primitives (PrimInt63/Uint63) used by
# CoqInterval's reflective computation. No custom/behavioural axioms. (Needs coq-interval.)
check_file Trigonometry_hardened.v \
  'functional_extensionality|sig_forall_dec|sig_not_dec|Classical_Prop|PrimInt63|Uint63' \
  Pi_double_precision_bounds

[ "$rc" -eq 0 ] && echo "ALL OK" || echo "FAILURES"
exit $rc
