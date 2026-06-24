/* ATT&CK: T1078 Valid Accounts
   H-S negative control: the forgotten-check bug. A maintenance endpoint calls
   the guarded op `sys_write` directly, without verifying the token first. The
   injected capability precondition (session_ok == 1) is unprovable at that
   call site -> red, in the caller that took the shortcut. */

//@ ghost int session_ok = 0;

/*@ assigns session_ok;
    ensures \result != 0 ==> session_ok == 1; */
int verify_token(int tok);

void sys_write(int v) { (void)v; }      /* the guarded operation */

/*@ happy \prop,
      \name("authn"),
      \targets({sys_write}),
      \context(\precond),
      session_ok == 1;
*/

void maintenance(int v)
{
  sys_write(v);                         /* no verify_token -> precondition fails (RED) */
}
