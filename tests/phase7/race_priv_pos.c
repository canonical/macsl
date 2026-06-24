/* WS1 stage 1 (H-E race): \guarded_by — POSITIVE control.
   The privilege field is shared mutable state; a TOCTOU race on it is a
   privilege-escalation path (one thread reads "user", another flips it to
   "admin" between the check and the act).  The correct path holds priv_lock
   while updating the field, so the injected `held(priv_lock)` holds.

   Scope: macsl proves the field is updated under the lock, NOT that the
   check-then-act on the privilege decision is atomic — stage 2 owes that. */

//@ ghost int priv_lock = 0;
/*@ axiomatic Lock { predicate held(integer l) reads l; } */

/*@ assigns priv_lock; ensures held(priv_lock); */
void acquire_priv(void);
/*@ assigns priv_lock; */
void release_priv(void);

int proc_priv = 0;         /* 0 = user, 1 = admin — shared */

/*@ happy \prop,
      \name("priv_guard"),
      \targets({set_priv}),
      \context(\guarded_by),
      held(priv_lock);
*/

void set_priv(int level)
{
  acquire_priv();          /* held(priv_lock) now holds */
  proc_priv = level;       /* guarded write -> green */
  release_priv();
}
