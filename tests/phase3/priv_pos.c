/* H-E positive control: privilege monotonicity. Outside the privilege gate,
   no function may END with higher privilege than it started.  Levels are
   encoded as ints (0 = user, 1 = admin; user < admin).

   - sudo_gate is EXEMPT (\diff(\ALL, {sudo_gate})) and may raise privilege.
   - do_work does not touch privilege            -> monotonicity holds.
   - drop only lowers privilege                  -> monotonicity holds. */

int proc_priv = 0;    /* 0 = user, 1 = admin */

/*@ happy \prop,
      \name("noesc"),
      \targets(\diff(\ALL, {sudo_gate})),
      \context(\postcond),
      proc_priv <= \old(proc_priv);
*/

void sudo_gate(void) { proc_priv = 1; }          /* exempt: the gate may raise */

void do_work(int x) { int y = x + 1; (void)y; }  /* never touches privilege */

void drop(void) { if (proc_priv > 0) proc_priv = proc_priv - 1; }  /* only lowers */
