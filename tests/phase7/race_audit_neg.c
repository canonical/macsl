/* ATT&CK: T1070 Indicator Removal (lost-update race drops an audit record)
   WS1 stage 1 (H-R race): \guarded_by — NEGATIVE control.
   The lost-update bug: a hot path appends to the shared audit log WITHOUT
   holding audit_lock, so two concurrent appenders can clobber each other's
   record.  macsl injects `held(audit_lock)` at the log write; unprovable -> RED.
   Without -macsl the program proves vacuously. */

//@ ghost int audit_lock = 0;
/*@ axiomatic Lock { predicate held(integer l) reads l; } */

/*@ assigns audit_lock; ensures held(audit_lock); */
void acquire_audit(void);

int log_slot = 0;

/*@ happy \prop,
      \name("audit_guard"),
      \targets({hot_append}),
      \context(\guarded_by),
      held(audit_lock);
*/

void hot_append(int rec)
{
  log_slot = rec;          /* NO acquire_audit -> held(audit_lock) fails (RED) */
}
