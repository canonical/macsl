#!/usr/bin/env bash
# Verify the coqwp hardening files: each compiles, and Print Assumptions on each
# lemma is either "Closed under the global context" or depends only on the
# whitelisted standard axiom functional_extensionality (declared per file below).
# Usage: ./check.sh   (expects the framac-coq8 opam env active)
set -u
cd "$(dirname "$0")"
WHY3="$(why3 --print-libdir)/coq"
rc=0

check_file () {            # <file> <allow_funext:0|1> <lemma...>
  local file="$1" allow="$2"; shift 2
  echo "== $file =="
  coqc -R "$WHY3" Why3 "$file" 2>/dev/null || { echo "  COMPILE FAILED"; rc=1; return; }
  local mod="${file%.v}"
  local out
  out="$({ echo "Require Import $mod."; for l in "$@"; do echo "Print Assumptions $l."; done; } \
          | coqtop -R "$WHY3" Why3 -Q . "" 2>/dev/null)"
  local closed funext bad
  closed=$(grep -c 'Closed under the global context' <<<"$out")
  funext=$(grep -c 'functional_extensionality' <<<"$out")
  # axiom-name lines are at column 0 and end in " :"; any such line that is not
  # functional_extensionality is an unexpected axiom.
  bad=$(grep -E '^[^ ].* :$' <<<"$out" | grep -vc 'functional_extensionality')
  echo "  lemmas=$# closed=$closed funext=$funext"
  if [ "$bad" -ne 0 ]; then echo "  FAIL: unexpected axiom"; rc=1; return; fi
  if [ "$allow" -eq 0 ] && [ "$funext" -ne 0 ]; then
    echo "  FAIL: functional_extensionality not allowed here"; rc=1; return
  fi
  echo "  OK"
}

check_file Memory_hardened.v 0 \
  separated_1 separated_included separated_trans eqmem_included eqmem_sym \
  havoc_access table_to_offset_zero table_to_offset_monotonic \
  int_of_addr_bijection addr_of_int_bijection addr_of_null

check_file Vset_hardened.v 1 \
  member_bool1 member_empty member_singleton member_union member_inter \
  union_empty inter_empty member_range member_range_sup member_range_inf \
  member_range_all

[ "$rc" -eq 0 ] && echo "ALL OK" || echo "FAILURES"
exit $rc
