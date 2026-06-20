/* FE10 silent audit saturation, isolated and PROVED.
   =======================================================================
   The EBIOS crosswalk flagged FE10 (G4, the headline residual): once the fixed
   audit log is FULL, a transfer that still moves money but can no longer append
   a record succeeds SILENTLY -- a permanent, undetected non-repudiation hole.
   main.c's nonrepud_complete (a balance changed => audit_len grew) holds only
   under `requires 0 <= audit_len < 1024`: it ASSUMES the log has room, i.e. the
   precondition assumes the threat away.

   The fix is FAIL-CLOSED: a transfer must REFUSE when the log cannot record it,
   so a balance change ALWAYS produces an audit record -- even at capacity. This
   driver proves exactly that on the clean integer model compliant.c uses: with
   the fail-closed guard, completeness (nonrepud_atcap) holds with the
   precondition RELAXED to allow a full log (0 <= audit_len <= NLOG). The matching
   silent-saturation attack (transfer_unlogged_atcap, no fail-closed guard) is the
   red control in attacks.c (ATTACK 10).

   main.c's real transfer now carries the same fail-closed guard (the runtime
   remediation); the at-capacity PROOF lives here, free of the string-keyed
   context bloat -- the audit_append_frame.c / rbac_horizontal.c driver pattern. */

#define NACC 8
#define NLOG 1024
int balance[NACC];
int audit[NLOG];
int audit_len = 0;

/* room-aware logger: records iff there is room, reporting whether it did. */
/*@ requires 0 <= audit_len <= NLOG;
    assigns audit[0 .. NLOG - 1], audit_len;
    ensures audit_len <= NLOG;
    behavior room:
      assumes audit_len < NLOG;
      ensures audit_len == \old(audit_len) + 1;
      ensures \result == 1;
    behavior full:
      assumes audit_len == NLOG;
      ensures audit_len == \old(audit_len);
      ensures \result == 0;
    complete behaviors;
    disjoint behaviors;
*/
int log_transfer(int from, int to, int amount);

/* fail-closed money operation: refuse if the audit log cannot record it. */
/*@ requires 0 <= from < NACC && 0 <= to < NACC;
    requires 0 <= audit_len <= NLOG;
    requires amount > 0;
    assigns balance[from], balance[to], audit[0 .. NLOG - 1], audit_len;
*/
int transfer(int from, int to, int amount)
{
  if (audit_len >= NLOG) return -1;     /* FAIL-CLOSED: no room to record -> refuse */
  if (balance[from] < amount) return -1;
  balance[from] -= amount;
  balance[to]   += amount;
  log_transfer(from, to, amount);       /* room guaranteed -> always records */
  return 0;
}

/* H-R non-repudiation at capacity (FE10): a balance changed ==> the audit log
   grew -- holding EVEN when the log may be full (the precondition allows
   audit_len == NLOG). The fail-closed guard makes the full case vacuous (no
   balance change), so no successful transfer is ever silently unrecorded. */
/*@ happy \prop, \name("nonrepud_atcap"),
      \targets({transfer}), \context(\postcond),
      (\exists integer i; 0 <= i < NACC && balance[i] != \old(balance[i]))
        ==> audit_len > \old(audit_len);
*/
