/* WS1 stage 1: \stable_check — POSITIVE control.
   A check-then-act whose guard reads shared state `g`.  macsl marks the act with
   `stable(g)` — the assertion that the guard value the check observed is still
   the value the act assumes (no interleaved writer changed it in between).  This
   is the MARKER THAT AN INTERLEAVING ARGUMENT IS OWED: stage 1 does NOT discharge
   atomicity; it forces the obligation to be visible and, here, established by a
   trusted snapshot primitive.

   `stable` is an UNINTERPRETED logic predicate (the macsl \stable marker). */

int g = 0;                 /* shared guard state, read by the check */
/*@ axiomatic Stable { predicate stable(integer x) reads x; } */

/* trusted: takes an atomic snapshot of the guard under a lock and ESTABLISHES
   that the observed value is stable for the act that follows. */
/*@ assigns \nothing; ensures stable(g); */
void snapshot_guard(void);

int out = 0;

/*@ happy \prop,
      \name("guard_stable"),
      \targets({check_then_act}),
      \context(\stable_check),
      stable(g);
*/

void check_then_act(void)
{
  snapshot_guard();        /* stable(g) now holds */
  if (g) out = 1;          /* act under the snapshot -> stable(g) discharged (green) */
}
