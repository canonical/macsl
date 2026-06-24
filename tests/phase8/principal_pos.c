/* Phase B / WS3 (M-3): \authorized — POSITIVE control (genuine principal).

   Where H-S/\precond only proved "you called the checker", M-3 binds the
   protected operation to a PRINCIPAL IDENTITY: the obligation injected at the
   write site is `authorized(current_principal, OP_WRITE)` over an UNINTERPRETED
   `authorized` predicate.  Here the caller runs `authenticate()`, whose trusted
   declaration-only contract ESTABLISHES that the *current* principal is genuine
   and authorized for OP_WRITE, so the obligation discharges (green).

   `authorized` carries NO behavioural axiom — the actual token/identity check
   is the trusted boundary (GH1), exactly like verify_token in H-S.  macsl
   proves "the principal is bound at the op", not that the token scheme is
   unforgeable.  See docs/usage.md "Principal identity (WS3)". */

#define OP_WRITE 1

int current_principal = 0;       /* the running principal id (shared) */
/*@ axiomatic Principal { predicate authorized(integer p, integer op) reads p; } */

/* trusted identity oracle: declaration-only.  Authenticating ESTABLISHES that
   the current principal is genuinely authorized for OP_WRITE — this is the
   boundary the real token check (whoami()) discharges. */
/*@ assigns current_principal;
    ensures authorized(current_principal, OP_WRITE); */
void authenticate(void);

int protected_state = 0;         /* the resource the op mutates */

/*@ happy \prop,
      \name("principal_bound"),
      \targets({protected_op}),
      \context(\authorized),
      authorized(current_principal, OP_WRITE);
*/

void protected_op(int v)
{
  authenticate();                /* genuine principal now bound */
  protected_state = v;           /* protected write -> obligation discharged (green) */
}
