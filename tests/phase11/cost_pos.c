/* Phase C / WS5 (M-5): \context(\noninterference(\cost)) — POSITIVE control.

   Cost-channel noninterference: the relational TIMING variant of H-I2.  macsl
   extends the self-composition twin (emit_selfcomp) with a ghost STEP COUNTER
   (__macsl_cost, the same fuel cost model), synthesizing `cmp__costcomp` that
   runs cmp twice (public `attempt` shared, secret `stored` split a/b),
   resetting/snapshotting the counter around each call, and asserts the two
   STEP COUNTS are equal: `ca == cb`.  Where plain \noninterference checks the
   RESULT is secret-independent, this checks the WORK (branch/step count) is.

   The cost MODEL is macsl's (it injects __macsl_cost++ at each call step); the
   cost VALUE is carried by the FIXTURE's contract on cmp (the `ensures` names
   __macsl_cost) — exactly the WS4 split where `\hash`'s value lives in the
   trusted contract, not in a macsl axiom.  The counter is a ground ghost
   variable: NO ranking lemma, NO axiom (no TCB growth).

   Here cmp is CONSTANT-WORK: it makes the SAME number of call steps on every
   path, independent of the secret `stored`.  So __macsl_cost ends equal for the
   two runs -> `ca == cb` discharges -> green.  Bound: MODELLED steps, not
   wall-clock / cache / uarch (GH3). */

/*@ ghost int __macsl_cost; */    /* the cost channel (macsl's twin reads this) */

/* CONSTANT-WORK compare: the cost contract states the step count as a function
   of PUBLIC state ONLY (here a constant) — independent of the secret `stored`.
   So __macsl_cost ends equal for the two runs -> `ca == cb` discharges. */
/*@ assigns __macsl_cost;
    ensures __macsl_cost == \old(__macsl_cost) + 2; */
int cmp(int attempt, int stored);

/*@ happy \prop,
      \name("ct_cost"),
      \targets({cmp}),
      \context(\noninterference(\cost)),
      \secret(stored);
*/
