/* ATT&CK: T1070 Indicator Removal
   H-R negative control: sys_unlink changes the protected state `disk` but
   FORGETS to append to the audit log — "the deletion that left no trace".
   The completeness postcondition must be unprovable (red). */

int disk = 0;
//@ ghost int log_len = 0;

/*@ happy \prop,
      \name("audit"),
      \targets({sys_unlink}),
      \context(\postcond),
      \old(disk) != disk ==> log_len > \old(log_len);
*/

void sys_unlink(void)
{
  disk = 0;                 /* changes disk ... */
  /* ... but no  //@ ghost log_len++;  -> completeness violated */
}
