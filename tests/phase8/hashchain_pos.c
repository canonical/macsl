/* Phase B / WS4 (M-4): \tamper_evident — POSITIVE control (chain extended).

   The repudiation obligation is STRENGTHENED from a length predicate (H-R,
   "the log grew") to a HASH CHAIN: every committed record commits the running
   hash of its predecessor,

        logbuf[i].mac == H(logbuf[i-1].mac, logbuf[i].rec)   for 0 < i < len

   where H is the SINGLE uninterpreted logic function `\hash`.  `\hash` carries
   NO behavioural axiom (collision-resistance is the crypto residual, GH1 — NOT
   smuggled here); macsl proves only the CHAINING DISCIPLINE: a correct append
   recomputes the chain forward, so the postcondition holds.

   Here append_record links the new slot to its predecessor via the trusted
   compute_mac contract (\result == \hash(prev, rec)), so the chain invariant is
   preserved -> green.  See docs/usage.md "Tamper-evident log (WS4)". */

#define NLOG 8

struct entry { int rec; int mac; };
struct entry logbuf[NLOG];
int len = 0;

/* The SINGLE uninterpreted hash H of the chain.  Declared as a bodiless,
   axiom-free logic function (reads nothing) — exactly the WS1 discipline for
   `held`/`stable`.  macsl's `\hash` marker resolves to this symbol; it carries
   NO behavioural axiom (no injectivity, no collision-resistance) — that is the
   crypto residual (GH1), supplied as a hypothesis if ever needed, never as a
   smuggled axiom. */
/*@ axiomatic Hash { logic integer hash(integer prev, integer rec); } */

/* trusted MAC primitive: declaration-only, its body is the real crypto.  Its
   contract is the ONLY fact macsl uses about H — that compute_mac returns
   exactly hash(prev, rec). */
/*@ assigns \nothing;
    ensures \result == hash(prev, rec); */
int compute_mac(int prev, int rec);

/*@ happy \prop,
      \name("hashchain"),
      \targets({append_record}),
      \context(\tamper_evident),
      \forall integer i; 0 < i < len ==>
        logbuf[i].mac == \hash(logbuf[i-1].mac, logbuf[i].rec);
*/

/*@ requires 0 < len < NLOG;
    requires \forall integer i; 0 < i < len ==>
               logbuf[i].mac == hash(logbuf[i-1].mac, logbuf[i].rec);
    assigns len, logbuf[len];
*/
void append_record(int rec)
{
  logbuf[len].rec = rec;
  logbuf[len].mac = compute_mac(logbuf[len-1].mac, rec);  /* link to predecessor */
  len++;                                                   /* chain extended (green) */
}
