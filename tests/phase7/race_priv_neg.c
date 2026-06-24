/* ATT&CK: T1068 Exploitation for Privilege Escalation (unlocked TOCTOU priv flip)
   WS1 stage 1 (H-E race): \guarded_by — NEGATIVE control.
   The unlocked privilege flip: a helper sets the shared privilege field WITHOUT
   priv_lock, so a concurrent reader can observe a torn / escalated value.
   macsl injects `held(priv_lock)` at the write; unprovable -> RED.
   Without -macsl the program proves vacuously. */

//@ ghost int priv_lock = 0;
/*@ axiomatic Lock { predicate held(integer l) reads l; } */

/*@ assigns priv_lock; ensures held(priv_lock); */
void acquire_priv(void);

int proc_priv = 0;

/*@ happy \prop,
      \name("priv_guard"),
      \targets({raw_set_priv}),
      \context(\guarded_by),
      held(priv_lock);
*/

void raw_set_priv(int level)
{
  proc_priv = level;       /* NO acquire_priv -> held(priv_lock) fails (RED) */
}
