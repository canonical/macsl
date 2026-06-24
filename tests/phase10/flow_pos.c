/* Phase C / WS7 (M-7): \context(\flow) — POSITIVE control (legit_write).

   Lattice-parametric flow.  The user declares a partial order `leq` and an
   (uninterpreted) labelling `label(...)` of resources; macsl proves NO-FLOW-UP +
   ownership over THAT lattice.  At each write site macsl injects the policy's
   flow predicate — here `\leq(\label(&caller_data), \label(\lhost_written))`:
   you may write a target only with data whose label the target's label
   dominates (no high-to-low / no cross-tenant flow).

   `\leq` / `\label` stay UNINTERPRETED (macsl emits NO axioms about them).  The
   lattice ORDER axioms (refl/antisym/trans) are the USER's OWN structural
   axiomatic — definitional, satisfied by any partial order, like H-E's integer
   encoding — NOT a behavioural fact macsl smuggles.  The label VALUES come from
   a trusted boundary contract (`reclassify` below), exactly as `authenticate()`
   establishes `authorized` in WS3.

   Here the write goes to a target whose label dominates the caller's data label
   (established by the trusted `reclassify`), so the no-flow-up obligation
   discharges -> green.  This folds vertical EoP (no write-up) and horizontal
   RBAC (no cross-owner write) into ONE property over the lattice. */

int caller_data;     /* the value the caller wants to write */
int tenantA;         /* a labelled resource */

/*@ axiomatic Lattice {
      predicate leq(integer a, integer b);
      logic integer label(int *p);
      axiom refl:  \forall integer a; leq(a, a);
      axiom asym:  \forall integer a, b; leq(a,b) && leq(b,a) ==> a == b;
      axiom trans: \forall integer a, b, c; leq(a,b) && leq(b,c) ==> leq(a,c);
    } */

/* trusted relabel/declassify boundary (declaration-only): ESTABLISHES that the
   caller's data is now at or below the target's label.  This is the lattice
   analog of authenticate()'s ensures authorized(...). */
/*@ assigns caller_data;
    ensures leq(label(&caller_data), label(&tenantA)); */
void reclassify(void);

/*@ happy \prop,
      \name("noflowup"),
      \targets({legit_write}),
      \context(\flow),
      \leq(\label(&caller_data), \label(\lhost_written));
*/

void legit_write(void)
{
  reclassify();              /* trusted: caller_data now dominated by tenantA */
  tenantA = caller_data;     /* write-down (allowed): obligation discharges */
}
