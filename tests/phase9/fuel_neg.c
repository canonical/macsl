/* ATT&CK: T1499 Endpoint Denial of Service / algorithmic complexity
   Phase C / WS6 (M-6): \context(\fuel) — NEGATIVE control (algorithmic_dos).

   The bug: a terminating-but-input-superlinear path.  The work scales with the
   input (here the loop runs n*n times, each doing a call step), so the injected
   ghost step counter __macsl_fuel is NOT bounded by the supplied LINEAR budget
   `\fuel <= 100`.  macsl auto-frames the counter on the loop (it adds
   `__macsl_fuel` to the loop's assigns and a `0 <= __macsl_fuel` invariant), so
   the redness is genuinely about the BOUND, not a missing frame: the closing VC
   `__macsl_fuel <= 100` is UNPROVABLE -> RED.  This is the verified form of an
   algorithmic-complexity DoS: it returns, but it does unbounded work.

   The same function with a bound that matches its actual work (or after the
   algorithm is tightened to linear) discharges -> the bound is the load-bearing
   obligation.  Strip the policy (drop -macsl) and the program proves vacuously
   (no fuel goal at all): the red-without / green-with contrast. */

int helper(int x);

/*@ happy \prop,
      \name("fuelbound"),
      \targets({algorithmic_dos}),
      \context(\fuel),
      \fuel <= 100;
*/

/*@ requires n >= 0;
    terminates \true;
    assigns \nothing; */
int algorithmic_dos(int n)
{
  int s = 0;
  int bound = n * n;
  /*@ loop invariant 0 <= i <= bound;
      loop assigns i, s;
      loop variant bound - i; */
  for (int i = 0; i < bound; i++)   /* superlinear: n*n call steps */
    s += helper(i);
  return s;                         /* __macsl_fuel unbounded -> \fuel<=100 RED */
}
