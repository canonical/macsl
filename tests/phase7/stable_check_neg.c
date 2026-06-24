/* ATT&CK: T1574.010 / TOCTOU race (check-then-act on a non-stable guard)
   WS1 stage 1: \stable_check — NEGATIVE control.
   The bare check-then-act bug (TOCTOU): the guard `g` is read and acted on with
   NO snapshot / stability discipline, so an interleaved writer can change `g`
   between the check and the act.  macsl marks the act with `stable(g)`;
   unprovable -> RED.  Without -macsl the program proves vacuously.

   The RED here is exactly the macsl signal "a real interleaving argument is
   OWED and absent" — it must NOT be read as "the race is handled". */

int g = 0;                 /* shared guard state, read by the check */
/*@ axiomatic Stable { predicate stable(integer x) reads x; } */

/*@ assigns \nothing; ensures stable(g); */
void snapshot_guard(void);

int out = 0;

/*@ happy \prop,
      \name("guard_stable"),
      \targets({racy_check_then_act}),
      \context(\stable_check),
      stable(g);
*/

void racy_check_then_act(void)
{
  if (g) out = 1;          /* NO snapshot -> stable(g) fails (RED) */
}
