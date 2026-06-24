/* ATT&CK: T1499.004 Endpoint DoS: Application or System Exploitation
   H-D negative control: the confused parser (the teeth for totality). A crafted
   `len` drives a loop that only advances on odd `i`, so on even `i` it makes no
   progress and the loop variant `len - i` cannot be shown to strictly decrease ->
   the `\context(\total)` termination goal is RED. The verified form of "a
   malformed length field hangs the parser" — the classic denial-of-service.

   Extracted from small_example/attacks.c ATTACK 8. The compliant counterpart is
   phase6/totality_pos.c (same function, the progress bug removed). */

/*@ requires len >= 0; assigns \nothing; */
void parse_request(int len)
{
  int i = 0;
  /*@ loop invariant 0 <= i;
      loop assigns i;
      loop variant len - i;       // CANNOT be shown to decrease: even i makes no progress
  */
  while (i < len) { if (i % 2 == 1) i++; }   // even i: no progress -> no variant decrease

}

/* H-D availability: claimed, but the confused loop has no provable variant. */
/*@ happy \prop, \name("availability"),
      \targets({parse_request}), \context(\total),
      \true;
*/
