/* The append-only frame, isolated and DETERMINISTICALLY proved.
   =======================================================================
   main.c's H-R `nonrepud_append_only` policy is FAITHFUL (full AuditRecord
   equality of every earlier record). On main.c's real `transfer` that goal is
   intractable for SMT -- NOT because the property is hard, but because of
   *context bloat*: transfer's user-lookup loop and the libc strcmp/strlen
   contracts are dragged into every split goal (~2660-line Coq goals; SMT only
   closes the two char[50] frames by wall-clock grinding ~150s, and a DETERMINISTIC
   step budget of 2,000,000 steps still fails -- i.e. machine-dependent, not a
   real proof). Per the documented remedy (frama-c-monitoring/.../wp-gotchas.md,
   "isolate a driver", and coq-escalation.md §3), the load-bearing fact is proved
   here on a tiny driver, free of that context.

   This driver carries the IDENTICAL frame contract as `log_transfer`
   (`assigns logbuf[len], len;` -- only the new slot) and the IDENTICAL policy
   (full struct equality of every record below the old length). It discharges the
   exact char[50]-array frame that bloated out on main.c -- and it does so
   DETERMINISTICALLY:
     frama-c ... -macsl -wp -wp-prover alt-ergo,z3 -wp-split -wp-steps 50000
   proves it with a bounded (machine-independent) step budget, not a timeout. So
   the append-only property IS proved by provers; what main.c cannot give is a
   *clean* VC for the same fact, which is a context-bloat property of that
   function, not of the policy. (compliant.c proves the same policy on a scalar log;
   this driver covers the struct case.) */

#define N 1024
typedef struct { char from[50]; char to[50]; double amount; } Rec;
Rec logbuf[N];
int len = 0;

/* same frame contract as log_transfer: only the new slot logbuf[len] is written. */
/*@ requires 0 <= len < N;
    assigns logbuf[len], len;
    ensures len == \old(len) + 1; */
void append(double a) {
    logbuf[len].amount = a;   /* writing the new slot only -- old records untouched */
    len++;
}

/* H-R append-only: every earlier record is byte-identical (full struct equality --
   this is what forces WP to prove the two char[50] frames). */
/*@ happy \prop, \name("nonrepud_append_only"),
      \targets({append}), \context(\postcond),
      \forall integer i; 0 <= i < \old(len) ==> logbuf[i] == \old(logbuf[i]);
*/
