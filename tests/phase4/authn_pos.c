/* H-S positive control: check-before-use. The guarded op `sys_write` may be
   called only when the capability `session_ok` holds; `session_ok` is granted
   only by the trusted (declaration-only) `verify_token`. The authenticated
   caller checks the token first, so the injected call-site precondition holds. */

//@ ghost int session_ok = 0;

/* trusted token verifier: declaration-only contract (the identity check itself
   is NOT proved here — it is the trusted boundary the risk study carries). */
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

void handler(int tok, int v)
{
  if (verify_token(tok))
    sys_write(v);                       /* session_ok == 1 here -> precondition holds */
}
