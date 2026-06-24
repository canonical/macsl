/* ATT&CK: T1574.010 / TOCTOU race on shared session state
   WS1 stage 1 (H-S race): \guarded_by — NEGATIVE control.
   The check-then-act bug: a fast path mutates the shared session table WITHOUT
   taking session_lock first.  macsl injects `held(session_lock)` at the write
   site; it is unprovable on that path -> RED, in the function that took the
   shortcut.  Strip the policy (drop -macsl) and the program proves vacuously:
   that is the red-without / green-with-obligation contrast the control exists
   to demonstrate. */

//@ ghost int session_lock = 0;
/*@ axiomatic Lock { predicate held(integer l) reads l; } */

/*@ assigns session_lock; ensures held(session_lock); */
void acquire_session(void);

int session_table = 0;

/*@ happy \prop,
      \name("session_guard"),
      \targets({fast_touch}),
      \context(\guarded_by),
      held(session_lock);
*/

void fast_touch(int v)
{
  session_table = v;       /* NO acquire_session -> held(session_lock) fails (RED) */
}
