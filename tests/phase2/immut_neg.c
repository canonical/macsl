/* H-R append-only (immutability) negative control: `rewrite` overwrites an
   EXISTING log entry (logbuf[0]) — rewriting history. The append-only
   postcondition must be unprovable (red). */

//@ ghost int logbuf[100];
//@ ghost int log_len = 0;

/*@ happy \prop,
      \name("immut"),
      \targets({rewrite}),
      \context(\postcond),
      \forall integer i; 0 <= i < \old(log_len) ==> logbuf[i] == \old(logbuf[i]);
*/

void rewrite(int v)
{
  //@ ghost logbuf[0] = v;      /* overwrites history -> immutability violated */
}
