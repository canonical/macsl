/* FE11 token lifecycle, the DISCIPLINE half, isolated and PROVED.
   =======================================================================
   The EBIOS crosswalk flagged FE11 (G3): a session token accepted indefinitely
   (no expiry/revocation) or leaked and replayed lets an attacker impersonate the
   holder. FE11 has TWO halves and only one is in macsl's reach:

     (a) Token UNGUESSABILITY / cryptographic strength and the expiry CLOCK are
         irreducibly the TRUSTED BOUNDARY (spec §6) -- macsl does not prove a mock
         token is unguessable, nor model wall-clock expiry. This half stays an
         accepted residual.
     (b) The lifecycle DISCIPLINE -- a revoked / expired / replayed token must not
         AUTHORIZE an operation -- is a check-before-use property, and THAT is
         closeable. This driver proves (b): a protected operation runs only against
         a CURRENTLY-VALID token (token_active == 1 at the gate), so a stale or
         revoked token cannot drive it. The replay attack is the red control in
         attacks.c (ATTACK 11).

   main.c's authn already binds its capability to LIVE validity: handle_client
   grants session_authenticated only after get_role(token) != -1, a current-time
   lookup -- so revoking a token (clearing db[i].token) makes get_role fail and
   denies the capability. token_live makes that lifecycle discipline explicit and
   machine-checked; the unguessability + expiry-clock half (a) remains trusted.

   This is H-S (check-before-use) sharpened from "a session exists" to "the session
   rests on a token that is still valid NOW" -- the lifecycle companion to authn. */

#define NACC 8
int balance[NACC];
int session_ok = 0;     /* request-scoped capability */
int token_active = 0;   /* token lifecycle: 1 = currently valid; 0 = expired/revoked/absent */

/*@ requires 0 <= from < NACC && 0 <= to < NACC;
    assigns balance[from], balance[to]; */
void transfer(int from, int to, int amount)
{
  balance[from] -= amount;
  balance[to]   += amount;
}

/* H-S token lifecycle (FE11): a transfer runs only against a currently-valid
   token -- an expired or revoked token must not authorize it (no replay). */
/*@ happy \prop, \name("token_live"),
      \targets({transfer}), \context(\precond),
      token_active == 1;
*/

/* compliant handler: re-checks CURRENT validity before granting the capability
   and acting -- not merely "the token was once issued". */
/*@ requires 0 <= from < NACC && 0 <= to < NACC; */
void handle(int from, int to, int amount)
{
  session_ok = 0;
  if (token_active == 1) {       /* liveness check at request time (1 = valid) */
    session_ok = 1;
    transfer(from, to, amount);  /* reached only with a live token */
  }
}
