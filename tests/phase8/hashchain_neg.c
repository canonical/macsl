/* ATT&CK: T1565.001 / stored-data tampering — log splice
   Phase B / WS4 (M-4): \tamper_evident — NEGATIVE control (splice_log).

   The bug: an attacker REWRITES the record at an earlier slot (k < len-1) but
   leaves the mac chain unchanged — a splice/reorder that keeps the stored macs.
   The strengthened postcondition

        \forall i; 0 < i < len ==> logbuf[i].mac == \hash(logbuf[i-1].mac, logbuf[i].rec)

   no longer holds at slot k+1 (its predecessor's rec changed but the macs did
   not), so WP cannot prove it -> RED, catching the tamper.  An append-only +
   forward-recompute discipline (the positive twin) is the only way to satisfy
   it.

   Strip the policy (drop -macsl) and the program proves vacuously: that is the
   red-without / green-with-obligation contrast.

   CRYPTO RESIDUAL: `\hash` (= hash) is UNINTERPRETED.  macsl proves the
   CHAINING DISCIPLINE only; that an attacker cannot find a *second* preimage
   with the SAME mac (collision-resistance of H) is the trusted crypto boundary
   (GH1), NOT something macsl proves and NOT an axiom it smuggles. */

#define NLOG 8

struct entry { int rec; int mac; };
struct entry logbuf[NLOG];
int len = 0;

/*@ axiomatic Hash { logic integer hash(integer prev, integer rec); } */

/*@ assigns \nothing;
    ensures \result == hash(prev, rec); */
int compute_mac(int prev, int rec);

/*@ happy \prop,
      \name("hashchain"),
      \targets({splice_log}),
      \context(\tamper_evident),
      \forall integer i; 0 < i < len ==>
        logbuf[i].mac == \hash(logbuf[i-1].mac, logbuf[i].rec);
*/

/*@ requires 2 < len < NLOG;
    requires \forall integer i; 0 < i < len ==>
               logbuf[i].mac == hash(logbuf[i-1].mac, logbuf[i].rec);
    requires 0 < k < len - 1;
    assigns logbuf[k].rec;
*/
void splice_log(int k, int forged_rec)
{
  /* Overwrite an already-committed record but DO NOT recompute the chain:
     logbuf[k+1].mac == hash(logbuf[k].mac, logbuf[k+1].rec) now fails because
     logbuf[k].rec (hence the intended chain) changed but the macs are stale. */
  logbuf[k].rec = forged_rec;     /* chain broken -> postcondition RED */
}
