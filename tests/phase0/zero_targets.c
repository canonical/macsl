/* Vacuity check: the policy targets a function that has no write to match
   (an empty body), so macsl must emit the zero-expansion warning rather
   than silently "succeeding". */

int secret = 0;

/*@ happy \prop,
      \name("iso"),
      \targets({nothing}),
      \context(\writing),
      \separated(\written, &secret);
*/

void nothing(void)
{
  return;           /* no write site -> 0 assertions -> zero-expansion warning */
}
