/* Negative controls for the banking HAPPY policies: four attacks, each
   violating exactly one policy, each caught by `macsl -wp` (its goal red).
   Compare banking.c (the compliant system, all green). */

#define NACC  8
#define NLOG  1024

int balance[NACC];
int audit[NLOG];
int audit_len = 0;
int session_ok = 0;

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
