/* Positive control: no function writes the protected global `secret`,
   so every generated separation assertion holds (all goals proved). */

int secret = 0;
int a = 0;
int b = 0;

/*@ happy \prop,
      \name("iso"),
      \targets(\ALL),
      \context(\writing),
      \separated(\written, &secret);
*/

void only_public(void)
{
  a = 1;            /* \separated(&a, &secret) -> holds */
  b = a + 2;        /* \separated(&b, &secret) -> holds */
}
