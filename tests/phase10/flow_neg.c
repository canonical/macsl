/* ATT&CK: T1078 Valid Accounts / cross-tenant boundary violation
   Phase C / WS7 (M-7): \context(\flow) — NEGATIVE control (cross_tenant).

   The bug: a write that flows up / crosses an ownership boundary.  The caller's
   data is at a label the target does NOT dominate (a different tenant, or a
   higher classification), and NOTHING on the path established the no-flow-up
   relation `leq(label(&caller_data), label(&tenantA))` — there is no trusted
   reclassify on this path.  macsl injects that flow predicate at the write site;
   it is UNPROVABLE -> RED, in the function that crossed the boundary.

   The SAME write routed through the trusted reclassify gate (flow_pos.c) is
   green: the flow predicate is the load-bearing obligation.  Strip the policy
   (drop -macsl) and the program proves vacuously (no flow goal): the
   red-without / green-with contrast.

   This is the property that retires the FE2-style horizontal-RBAC workaround:
   the cross-account/cross-tenant write is caught by ONE lattice obligation, not
   a bespoke per-pair RBAC check. */

int caller_data;     /* the value the caller wants to write */
int tenantA;         /* a labelled resource owned by ANOTHER tenant */

/*@ axiomatic Lattice {
      predicate leq(integer a, integer b);
      logic integer label(int *p);
      axiom refl:  \forall integer a; leq(a, a);
      axiom asym:  \forall integer a, b; leq(a,b) && leq(b,a) ==> a == b;
      axiom trans: \forall integer a, b, c; leq(a,b) && leq(b,c) ==> leq(a,c);
    } */

/* declared but NOT called on the bug path */
/*@ assigns caller_data;
    ensures leq(label(&caller_data), label(&tenantA)); */
void reclassify(void);

/*@ happy \prop,
      \name("noflowup"),
      \targets({cross_tenant}),
      \context(\flow),
      \leq(\label(&caller_data), \label(\lhost_written));
*/

void cross_tenant(void)
{
  /* CROSS-TENANT: write another tenant's resource without establishing the
     flow relation -> leq(label(&caller_data), label(&tenantA)) unprovable. */
  tenantA = caller_data;     /* flow-up / cross-owner -> RED */
}
