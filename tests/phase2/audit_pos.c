/* H-R positive control: sys_write changes the protected state `disk` AND
   appends to the audit log (log_len++), so the completeness postcondition
   "if disk changed, the log grew" is provable. */

int disk = 0;
//@ ghost int log_len = 0;

/*@ happy \prop,
      \name("audit"),
      \targets({sys_write}),
      \context(\postcond),
      \old(disk) != disk ==> log_len > \old(log_len);
*/

void sys_write(int v)
{
  disk = v;
  /* every protected change is logged: */
  //@ ghost log_len ++;
}
