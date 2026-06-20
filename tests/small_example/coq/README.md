# Coq escalation of the strncpy `valid_read_nstring` goal — result

`strlen_frame_proof.v` is the WP-generated goal
`log_transfer_call_strncpy_2_requires_valid_nstring_src` (preserve
`valid_read_nstring(to,49)` across the first `strncpy`'s writes) with a
hand-written proof. It **compiles** (`coqc` exit 0).

It is COMPLETE except for **exactly three `is_sint8 (t3 (shift a1 k))`**
obligations (marked `admit`), which is why the file ends in `Admitted`, NOT
`Qed`. It is therefore **not** a closing script and is deliberately kept OUT of
the WP session (a replay must never count it as proved).

What the proof establishes (all machine-checked here):
- base of the audit slot is the `audit_log` global (4454); `to`'s base != 4454;
- FRAME lemmas: after the first strncpy, the char/init maps agree with the
  originals on every address of `to`'s base (via object-distinctness +
  `memcpy'def` + `Map.set'def`);
- the RIGHT (init-based) disjunct of `valid_read_nstring` closes by separation
  ALONE — no `is_sint8`;
- the LEFT (`valid_read_string`) disjunct reduces correctly to a strlen frame
  whose ONLY residue is `is_sint8` of the string bytes.

Why the 3 `is_sint8` cannot be discharged (root cause):
- every `Q_strlen_*` axiom is guarded by `is_sint8 (Mchar (shift s i))`;
- the only hypothesis that could supply char-typing is `sconst t3`, and WP's own
  realization `$(frama-c -print-share-path)/wp/coqwp/Memory.v` defines
  `sconst` as **`Admitted`** (opaque). So the byte-typing invariant is NOT
  exposed to the Coq backend — which is why `-wp-prover coq` itself returns
  `[Unknown]`, not just the SMT provers.

Conclusion: this goal is a MEMORY-MODEL FRAMING obligation that WP's Coq backend
cannot discharge either (a known weak spot for string/`strlen` goals). It is the
wrong escalation target; the sound resolutions are a C-side restructure
(dissolve) or accepting it as a precisely-characterised residual. No axiom/admit
was smuggled into any verified result; the macsl policy stands at transfer 51/51.
