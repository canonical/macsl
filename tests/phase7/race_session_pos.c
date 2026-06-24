/* WS1 stage 1 (H-S race): \guarded_by — POSITIVE control.
   The session table is shared mutable state.  A correct handler ACQUIRES the
   session lock before touching it, so the macsl-injected `held(session_lock)`
   obligation at the write site holds.

   `held` is an UNINTERPRETED logic predicate (declared here, reused as the
   macsl \held marker): macsl proves only "the lock is held at the access",
   never that the acquire/release protocol is itself race-free — that atomicity
   argument is OWED to WS1 stage-2 (rely-guarantee).  See docs/usage.md
   "Concurrency (WS1 stage 1)". */

//@ ghost int session_lock = 0;
/*@ axiomatic Lock { predicate held(integer l) reads l; } */

/* trusted lock primitive: declaration-only.  Acquiring the lock ESTABLISHES
   `held` — this is the boundary the rely-guarantee argument (stage 2) discharges. */
/*@ assigns session_lock; ensures held(session_lock); */
void acquire_session(void);

/*@ assigns session_lock; */
void release_session(void);

int session_table = 0;     /* the shared state guarded by session_lock */

/*@ happy \prop,
      \name("session_guard"),
      \targets({touch_session}),
      \context(\guarded_by),
      held(session_lock);
*/

void touch_session(int v)
{
  acquire_session();       /* held(session_lock) now holds */
  session_table = v;       /* guarded write -> obligation discharged (green) */
  release_session();
}
