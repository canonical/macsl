/* H-R append-only (immutability) positive control: `append` writes only the
   NEW slot logbuf[log_len], so every old log entry is preserved — the
   append-only postcondition is provable. */

//@ ghost int logbuf[100];
//@ ghost int log_len = 0;

/*@ happy \prop,
      \name("immut"),
      \targets({append}),
      \context(\postcond),
      \forall integer i; 0 <= i < \old(log_len) ==> logbuf[i] == \old(logbuf[i]);
*/

void append(int v)
{
  //@ ghost logbuf[log_len] = v;
  //@ ghost log_len ++;
}
