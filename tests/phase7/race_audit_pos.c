/* WS1 stage 1 (H-R race): \guarded_by — POSITIVE control.
   The audit log is shared mutable state.  Two threads appending concurrently
   without a lock can interleave and drop a record (a lost-update repudiation
   race).  The correct appender takes audit_lock before writing the log slot, so
   the injected `held(audit_lock)` holds.

   macsl proves lock-held-at-the-log-write ONLY; it does NOT prove the
   append sequence is atomic across the interleaving — that is OWED to stage 2. */

//@ ghost int audit_lock = 0;
/*@ axiomatic Lock { predicate held(integer l) reads l; } */

/*@ assigns audit_lock; ensures held(audit_lock); */
void acquire_audit(void);
/*@ assigns audit_lock; */
void release_audit(void);

int log_slot = 0;          /* shared audit log cell */

/*@ happy \prop,
      \name("audit_guard"),
      \targets({append_record}),
      \context(\guarded_by),
      held(audit_lock);
*/

void append_record(int rec)
{
  acquire_audit();         /* held(audit_lock) now holds */
  log_slot = rec;          /* guarded write -> green */
  release_audit();
}
