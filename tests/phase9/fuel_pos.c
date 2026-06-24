/* Phase C / WS6 (M-6): \context(\fuel) — POSITIVE control (bounded_work).

   \fuel is a bounded-WORK budget: macsl injects a ghost STEP COUNTER
   (__macsl_fuel) into the body, ++'d at each loop back-edge and call site, and
   emits the policy bound `\fuel <= N` as a CHECKED postcondition.  `\fuel` is a
   per-site META-TERM resolving to the injected counter, so the bound is an
   ordinary inequality over a real ghost variable — NO new logic symbol, NO
   ranking lemma, NO axiom (a ground per-site counter; no TCB growth).

   Here the work is straight-line: exactly three call steps, so __macsl_fuel == 3
   at return and the supplied bound `\fuel <= 4` discharges -> green.  This is
   the bounded-iteration claim \total deliberately omits: not just "it
   terminates", but "it does at most N steps of work". */

int helper(int x);

/*@ happy \prop,
      \name("fuelbound"),
      \targets({bounded_work}),
      \context(\fuel),
      \fuel <= 4;
*/

int bounded_work(int n)
{
  int a = helper(n);       /* step 1 */
  int b = helper(a);       /* step 2 */
  int c = helper(b);       /* step 3 */
  return c;                /* __macsl_fuel == 3 <= 4 -> green */
}
