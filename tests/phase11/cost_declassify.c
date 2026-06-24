/* Phase C / WS5 (M-5): \declassify — the AUDITED RELEASE POINT.

   `\declassify(v)` names a value whose release is DELIBERATE and ON RECORD: a
   policy that lists it is declaring "I intend to release v" so the release is
   never silent.  macsl records it (an audit feedback note: "cmp declassifies
   {attempt} (audited release point)") and still synthesizes the cost twin — the
   release is explicit, auditable, and reviewable, which is the whole point of a
   declassifier vs. a silent leak.

   Here cmp is constant-work in the secret (so `ca == cb` discharges), and the
   policy additionally declares `attempt` a declassified public input — the
   audit trail a reviewer needs to confirm the release was intended.  See
   docs/usage.md "Cost-channel NI (WS5)" for the \declassify audit semantics and
   the honest scope note (the cost channel relaxes per AGGREGATE step count; a
   per-value structural exemption is the value-channel form). */

/*@ ghost int __macsl_cost; */

/*@ assigns __macsl_cost;
    ensures __macsl_cost == \old(__macsl_cost) + 2; */
int cmp(int attempt, int stored);

/*@ happy \prop,
      \name("ct_cost"),
      \targets({cmp}),
      \context(\noninterference(\cost)),
      \secret(stored),
      \declassify(attempt);
*/
