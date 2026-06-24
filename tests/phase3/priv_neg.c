/* ATT&CK: T1068 Exploitation for Privilege Escalation
   H-E negative control: the confused deputy. `escalate` is a non-gate function
   reachable from unprivileged code that raises privilege to admin. The
   monotonicity postcondition (proc_priv <= \old(proc_priv)) must be unprovable
   for it (red) — caught in the function that took the shortcut. */

int proc_priv = 0;    /* 0 = user, 1 = admin */

/*@ happy \prop,
      \name("noesc"),
      \targets(\diff(\ALL, {sudo_gate})),
      \context(\postcond),
      proc_priv <= \old(proc_priv);
*/

void sudo_gate(void) { proc_priv = 1; }          /* exempt */

void escalate(void) { proc_priv = 1; }           /* NON-gate: raises priv -> RED */
