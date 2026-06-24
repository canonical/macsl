/* ATT&CK: T1134 / forged-principal — privilege misattribution
   Phase B / WS3 (M-3): \authorized — NEGATIVE control (forged_principal).

   The bug: the protected operation runs against a FORGED / literal principal
   (set by assignment, not established by the trusted authenticate() contract).
   macsl injects `authorized(current_principal, OP_WRITE)` at the protected
   write site; on this path nothing established it -> UNPROVABLE -> RED, in the
   function that forged the identity.

   Strip the policy (drop -macsl) and the program proves vacuously: that is the
   red-without / green-with-obligation contrast the control exists to show.
   This is the point WS3 makes over H-S: H-S would be satisfied by "some check
   ran"; here a forged literal principal still fails `authorized`. */

#define OP_WRITE 1

int current_principal = 0;
/*@ axiomatic Principal { predicate authorized(integer p, integer op) reads p; } */

/* declared but NOT called on the bug path */
/*@ assigns current_principal;
    ensures authorized(current_principal, OP_WRITE); */
void authenticate(void);

int protected_state = 0;

/*@ happy \prop,
      \name("principal_bound"),
      \targets({forged_principal}),
      \context(\authorized),
      authorized(current_principal, OP_WRITE);
*/

void forged_principal(int v)
{
  /* FORGED: claim an identity by fiat, skipping the trusted authenticate()
     contract.  `authorized(current_principal, OP_WRITE)` is never established. */
  protected_state = v;           /* authorized(.., OP_WRITE) unprovable -> RED */
}
