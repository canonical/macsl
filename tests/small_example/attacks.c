/* Negative controls for the banking HAPPY policies: four attacks, each
   violating exactly one policy, each caught by `macsl -wp` (its goal red).
   Compare compliant.c (the compliant system, all green). */

#define NACC  8
#define NLOG  1024

int balance[NACC];
int audit[NLOG];
int audit_len = 0;
int session_ok = 0;
int role[NACC];         /* privilege level: 0 = super-admin .. 2 = user (smaller = more) */
int pin[NACC];          /* H-I1: confidential per-account PIN */
int leak_sink = 0;      /* a public sink an attacker exfiltrates into */
int caller_acct = 0;    /* request-scoped caller account (see rbac_horizontal.c) */

/*@ assigns session_ok; ensures \result != 0 ==> session_ok == 1; */
int authenticate(int user, int pass);

/*@ requires 0 <= audit_len < NLOG;
    assigns audit[audit_len], audit_len;
    ensures audit_len == \old(audit_len) + 1;
    ensures \forall integer i; 0 <= i < \old(audit_len) ==> audit[i] == \old(audit[i]);
*/
void log_transfer(int from, int to, int amount);

/* a compliant transfer (defined so the H-S call-site check has a callee) */
/*@ requires 0 <= from < NACC && 0 <= to < NACC;
    requires 0 <= audit_len < NLOG;
    assigns balance[from], balance[to], audit[audit_len], audit_len;
*/
void transfer(int from, int to, int amount)
{
  balance[from] -= amount;
  balance[to]   += amount;
  log_transfer(from, to, amount);
}

/* ATTACK 1 — H-R completeness: moves money but never logs it
   ("the transfer that left no trace"). */
/*@ requires 0 <= from < NACC && 0 <= to < NACC;
    assigns balance[from], balance[to]; */
void transfer_silent(int from, int to, int amount)
{
  balance[from] -= amount;
  balance[to]   += amount;
}
/*@ happy \prop, \name("nonrepud_complete"),
      \targets({transfer_silent}), \context(\postcond),
      (\exists integer i; 0 <= i < NACC && balance[i] != \old(balance[i]))
        ==> audit_len > \old(audit_len);
*/

/* ATTACK 2 — H-R append-only: overwrites an existing audit record
   (rewriting history). */
/*@ requires 0 < audit_len <= NLOG;
    assigns audit[0]; */
void rewrite_audit(int v) { audit[0] = v; }
/*@ happy \prop, \name("nonrepud_append_only"),
      \targets({rewrite_audit}), \context(\postcond),
      \forall integer i; 0 <= i < \old(audit_len) ==> audit[i] == \old(audit[i]);
*/

/* ATTACK 3 — H-T integrity: a non-transfer function writes a balance directly. */
/*@ requires 0 <= i < NACC;
    assigns balance[i]; */
void tamper(int i, int v) { balance[i] = v; }
/*@ happy \prop, \name("bal_integrity"),
      \targets({tamper}), \context(\writing),
      \separated(\written, balance + (0 .. NACC - 1));
*/

/* ATTACK 4 — H-S: an endpoint reaching transfer without authenticating first. */
/*@ requires 0 <= from < NACC && 0 <= to < NACC;
    requires 0 <= audit_len < NLOG;
    assigns balance[from], balance[to], audit[audit_len], audit_len; */
void unauth_endpoint(int from, int to, int amount)
{
  transfer(from, to, amount);          /* no authenticate -> call-site precond red */
}
/*@ happy \prop, \name("authn"),
      \targets({transfer}), \context(\precond),
      session_ok == 1;
*/

/* ATTACK 5 — H-E privilege escalation (the confused deputy): a helper reachable
   from unprivileged code that LOWERS a user's role (grants super-admin), so the
   account ends with more privilege than it began. The monotonicity postcondition
   role[k] >= \old(role[k]) goes red at this function. (Compliant counterpart: the
   priv_monotonic policy on main.c's transfer, which never raises a role.) */
/*@ requires 0 <= i < NACC;
    requires role[i] >= 1;            // currently below super-admin
    assigns role[i]; */
void escalate(int i) { role[i] = 0; }    /* confused deputy: grant super-admin */
/*@ happy \prop, \name("priv_monotonic"),
      \targets({escalate}), \context(\postcond),
      \forall integer k; 0 <= k < NACC ==> role[k] >= \old(role[k]);
*/

/* ATTACK 6 — H-I1 read confinement: a function that READS a confidential PIN
   into a public sink (the classic exfiltration). The read-separation check at
   `pin[i]` is unprovable -> red. */
/*@ requires 0 <= i < NACC; assigns leak_sink; */
void leak_pin(int i) { leak_sink = pin[i]; }   /* reads a secret -> read-check red */
/*@ happy \prop, \name("pin_confidential"),
      \targets({leak_pin}), \context(\reading),
      \separated(\read, pin + (0 .. NACC - 1));
*/

/* ATTACK 7 — H-I2 noninterference: `check`'s public result DEPENDS on the secret
   `stored` (returns attempt + stored). The synthesized self-composition's
   relational assert (equal public input, distinct secret -> equal result) is
   unprovable -> red. The verified form of the classic password-oracle leak. */
/*@ assigns \nothing; ensures \result == attempt + stored; */
int check(int attempt, int stored);
/*@ happy \prop, \name("noleak"),
      \targets({check}), \context(\noninterference),
      \secret(stored);
*/

/* ATTACK 8 — H-D denial of service (the confused parser): a crafted `len` drives
   a loop that fails to make progress on some inputs (it only advances on odd i),
   so the loop variant cannot be shown to strictly decrease -> the termination
   goal is red. The verified form of "a malformed length field hangs the parser." */
/*@ requires len >= 0; assigns \nothing; */
void parse_request(int len)
{
  int i = 0;
  /*@ loop invariant 0 <= i;
      loop assigns i;
      loop variant len - i; */
  while (i < len) { if (i % 2 == 1) i++; }   /* even i: no progress -> no decrease */
}
/*@ happy \prop, \name("availability"),
      \targets({parse_request}), \context(\total),
      \true;
*/

/* ATTACK 9 — H-E horizontal access control (FE2, the broken-access-control deputy):
   a transfer that OMITS the own-account guard, so a role-2 (User) caller can debit
   a FOREIGN account (from != caller_acct). The rbac_own_account postcondition
   (a role-2 caller decreases no account but its own) goes red. The verified form of
   "a User moved money out of someone else's account." Compliant counterpart:
   rbac_horizontal.c's guarded transfer. */
/*@ requires 0 <= caller_acct < NACC && 0 <= from < NACC && 0 <= to < NACC;
    requires 0 <= audit_len < NLOG;
    requires amount > 0;
    assigns balance[from], balance[to], audit[audit_len], audit_len; */
int transfer_cross(int from, int to, int amount)
{
  /* NO horizontal-RBAC gate: a User may debit ANY account -> broken access control */
  if (balance[from] < amount) return -1;
  balance[from] -= amount;
  balance[to]   += amount;
  log_transfer(from, to, amount);
  return 0;
}
/*@ happy \prop, \name("rbac_own_account"),
      \targets({transfer_cross}), \context(\postcond),
      role[caller_acct] == 2 ==>
        \forall integer a; 0 <= a < NACC && a != caller_acct ==>
          balance[a] >= \old(balance[a]);
*/
