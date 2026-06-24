/* ATT&CK: T1040 / timing side channel (constant-result, secret-dependent work)
   Phase C / WS5 (M-5): \context(\noninterference(\cost)) — NEGATIVE control
   (timing_oracle).

   The bug: the RESULT is constant (no value leak — plain \noninterference would
   pass), but the BRANCH/STEP COUNT depends on the secret.  Here cmp early-exits
   when `stored == attempt`, so it makes a secret-dependent number of call steps:
   the macsl cost counter __macsl_cost ends DIFFERENT for two runs with the same
   public `attempt` but distinct secrets.  The synthesized cost twin's relational
   assert `ca == cb` is UNPROVABLE -> RED.  This is the verified form of the
   classic timing oracle: an early-return compare that leaks via WORK, not value.

   Make the work secret-INDEPENDENT (the constant-time form, cost_pos.c) and it
   discharges -> `ca == cb` is the load-bearing obligation.  Strip the policy
   (drop -macsl) and the program proves vacuously (no cost twin): the
   red-without / green-with contrast. */

/*@ ghost int __macsl_cost; */    /* the cost channel (macsl's twin reads this) */

/* SECRET-DEPENDENT WORK: the cost contract records that the step count depends
   on the secret (an early-return compare: 1 step on the match path, 2 otherwise)
   while the RESULT is the constant 0.  Plain \noninterference (result) would
   PASS; the cost twin's `ca == cb` is unprovable across distinct secrets -> RED:
   the verified form of an early-return timing oracle. */
/*@ assigns __macsl_cost;
    ensures __macsl_cost ==
      \old(__macsl_cost) + (attempt == stored ? 1 : 2);
    ensures \result == 0; */
int cmp(int attempt, int stored);

/*@ happy \prop,
      \name("ct_cost"),
      \targets({cmp}),
      \context(\noninterference(\cost)),
      \secret(stored);
*/
