/* FE2 horizontal access control, isolated and PROVED.
   =======================================================================
   The EBIOS crosswalk (ebios-crosswalk.md) flagged FE2 as a coverage gap:
   "a role-2 (User) caller may debit ONLY their own account" is enforced in
   main.c's transfer BODY (the `role==2 && from!=caller` guard) but was never
   stated as a HAPPY hyperproperty. On main.c's real string-keyed transfer the
   postcondition context-bloats -- the caller-lookup loop and the libc strcmp/
   strlen contracts drag into every split goal, the same documented cost that
   scopes nonrepud_append_only onto audit_append_frame.c. So the load-bearing
   fact is proved here on the SAME clean integer-ledger model compliant.c uses,
   free of that context: the property holds (green), and the matching cross-
   account attack is the red control in attacks.c (ATTACK 9).

   As with H-S authn on main.c (a file-level happy policy cannot name a function
   PARAMETER -- WP: "unbound logic variable"), the caller's identity is modelled
   as a request-scoped GLOBAL capability `caller_acct`: the account index of the
   authenticated caller, set by the handler before transfer (mirroring main.c's
   `session_authenticated`). That is what makes the horizontal-RBAC property
   expressible at file scope.

   This is H-E (Elevation of privilege) in its HORIZONTAL form -- broken access
   control across peers, complementary to main.c's priv_monotonic which forbids
   VERTICAL escalation (raising a role). Together they close the authorization
   surface: no caller gains a higher tier (priv_monotonic) and no User-tier
   caller acts outside its own account (rbac_own_account). */

#define NACC 8
#define NLOG 1024

int balance[NACC];     /* account balances */
int audit[NLOG];       /* audit log */
int audit_len = 0;
int role[NACC];        /* privilege: 0 = super-admin .. 2 = user (smaller = more) */
int caller_acct = 0;   /* request-scoped capability: the authenticated caller's
                          account index (set by the handler before transfer) */

/*@ requires 0 <= audit_len < NLOG;
    assigns audit[audit_len], audit_len;
    ensures audit_len == \old(audit_len) + 1;
*/
void log_transfer(int from, int to, int amount);

/* The access-controlled money operation. Horizontal access control: a User
   (role 2) may debit ONLY their own account (from == caller_acct); a privileged
   caller (role < 2) may debit any account. */
/*@ requires 0 <= caller_acct < NACC && 0 <= from < NACC && 0 <= to < NACC;
    requires 0 <= audit_len < NLOG;
    requires amount > 0;
    assigns balance[from], balance[to], audit[audit_len], audit_len;
*/
int transfer(int from, int to, int amount)
{
  /* the horizontal-RBAC gate: a User may not debit a foreign account */
  if (role[caller_acct] == 2 && from != caller_acct) return -1;  /* reject cross-account */
  if (balance[from] < amount) return -1;                         /* insufficient funds */
  balance[from] -= amount;
  balance[to]   += amount;
  log_transfer(from, to, amount);
  return 0;
}

/* H-E horizontal access control (FE2): when the caller is a role-2 (User), NO
   account other than the caller's own is ever debited (its balance never
   decreases) -- on any path. On the reject path nothing changes; on the success
   path the role-2 guard forces from == caller_acct, so the only decreased account
   is the caller itself, and every other account is left unchanged or credited.
   (Stated unconditionally, like priv_monotonic -- a macsl \postcond predicate
   does not bind \result; it need not, since the law holds on every execution.) */
/*@ happy \prop, \name("rbac_own_account"),
      \targets({transfer}), \context(\postcond),
      role[caller_acct] == 2 ==>
        \forall integer a; 0 <= a < NACC && a != caller_acct ==>
          balance[a] >= \old(balance[a]);
*/
