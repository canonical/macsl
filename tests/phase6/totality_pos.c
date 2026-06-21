/* H-D positive control: totality (denial-of-service resistance). A request
   parser whose loop ALWAYS makes progress. `\context(\total)` turns
   "this function returns on EVERY input (and -wp-rte: faults on none)" into a
   checked claim: \total attaches a `terminates` clause WP must discharge from the
   loop variant. Here `i` advances every iteration, so the variant `len - i`
   strictly decreases and termination proves.

   The compliant counterpart to phase6/totality_neg.c (the confused parser whose
   variant cannot decrease) and the clean analogue of
   small_example/strtok_terminates.c (the real get_query_param gap, fixed). */

/*@ requires len >= 0; assigns \nothing; */
void parse_request(int len)
{
  int i = 0;
  /*@ loop invariant 0 <= i;
      loop assigns i;
      loop variant len - i;       // strictly decreases: i advances every iteration
  */
  while (i < len) { i++; }         // always makes progress -> terminates
}

/* H-D availability: the parse loop always terminates (and -wp-rte: never faults). */
/*@ happy \prop, \name("availability"),
      \targets({parse_request}), \context(\total),
      \true;
*/
