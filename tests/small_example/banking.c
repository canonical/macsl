/* HAPPY policies for the small_example banking backend, on a focused,
   fully-contracted distillation of main.c's security-relevant core
   (auth / transfer / audit).

   NB: main.c is NOT beyond WP. Frama-C's ACSL libc specifies the functions it
   uses -- strcmp/strncpy/strchr/strtok/strlen (string.h), read/write/close
   (unistd.h), socket/bind/listen/accept (sys/socket.h) -- and the variadic
   snprintf/sscanf are handled by the Variadic plugin. A clean WP proof of
   main.c is a matter of loop invariants plus the coarse (assigns/\from,
   bounded-result) nature of those library specs -- effort, not impossibility.
   banking.c is simply a crisp, fully-specified core that makes the policy
   demonstration unambiguous.

   This file is the COMPLIANT system: every policy holds (all goals proved).
   banking_attacks.c is the matching set of negative controls. */

#define NACC  8
#define NLOG  1024

int balance[NACC];      /* account balances */
int audit[NLOG];        /* audit log records (schematic) */
int audit_len = 0;      /* number of audit records written so far */
int session_ok = 0;     /* capability: an authenticated session is established */
int requests = 0;       /* a benign counter (non-protected state) */
int pin[NACC];          /* H-I1: confidential per-account PIN -- no app code may read it */

/* --- a login check whose PUBLIC result must not depend on the stored secret
   (H-I2 noninterference). Declaration-only with a functional contract: its result
   is a function of the public `attempt` alone. --- */
/*@ assigns \nothing; ensures \result == attempt; */
int check(int attempt, int stored);

/* --- trusted authenticator: declaration-only; grants the session capability.
   The identity check itself is the trusted boundary (EBIOS GH1) — macsl proves
   only the discipline around it. --- */
/*@ assigns session_ok;
    ensures \result != 0 ==> session_ok == 1; */
int authenticate(int user, int pass);

/* --- THE LOGGING FUNCTION (non-repudiation): appends exactly one audit record
   in the new slot, leaving every earlier record untouched. --- */
/*@ requires 0 <= audit_len < NLOG;
    assigns audit[audit_len], audit_len;
    ensures audit_len == \old(audit_len) + 1;
    ensures \forall integer i; 0 <= i < \old(audit_len) ==> audit[i] == \old(audit[i]);
*/
void log_transfer(int from, int to, int amount);

/* --- the money-moving operation: every transfer is logged --- */
/*@ requires 0 <= from < NACC && 0 <= to < NACC;
    requires 0 <= audit_len < NLOG;
    assigns balance[from], balance[to], audit[audit_len], audit_len;
*/
void transfer(int from, int to, int amount)
{
  balance[from] -= amount;
  balance[to]   += amount;
  log_transfer(from, to, amount);     /* every protected change is recorded */
}

/* ============================ HAPPY policies ============================ */

/* H-R non-repudiation (completeness): if any balance changed, the log grew. */
/*@ happy \prop, \name("nonrepud_complete"),
      \targets({transfer}), \context(\postcond),
      (\exists integer i; 0 <= i < NACC && balance[i] != \old(balance[i]))
        ==> audit_len > \old(audit_len);
*/

/* H-R non-repudiation (append-only): old audit records are never rewritten. */
/*@ happy \prop, \name("nonrepud_append_only"),
      \targets({transfer}), \context(\postcond),
      \forall integer i; 0 <= i < \old(audit_len) ==> audit[i] == \old(audit[i]);
*/

/* H-S check-before-use: transfer may be called only on an authenticated session. */
/*@ happy \prop, \name("authn"),
      \targets({transfer}), \context(\precond),
      session_ok == 1;
*/

/* H-T integrity: nothing but transfer may write account balances. */
/*@ happy \prop, \name("bal_integrity"),
      \targets(\diff(\ALL, {transfer})), \context(\writing),
      \separated(\written, balance + (0 .. NACC - 1));
*/

/* H-I1 read confinement: no application code reads the confidential PIN. */
/*@ happy \prop, \name("pin_confidential"),
      \targets(\ALL), \context(\reading),
      \separated(\read, pin + (0 .. NACC - 1));
*/

/* H-I2 noninterference: check's public result is independent of the secret
   `stored` (macsl self-composes check and proves the two results equal). */
/*@ happy \prop, \name("noleak"),
      \targets({check}), \context(\noninterference),
      \secret(stored);
*/

/* A compliant client: authenticates first, then transfers within bounds. */
void client(int from, int to, int amount)
{
  requests += 1;                      /* benign write (separated from balances) */
  if (0 <= from && from < NACC && 0 <= to && to < NACC
      && 0 <= audit_len && audit_len < NLOG) {
    if (authenticate(from, amount))
      transfer(from, to, amount);
  }
}
