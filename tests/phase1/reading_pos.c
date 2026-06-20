/* H-I1 positive control: no targeted function reads `secret`, so every
   generated read-separation assertion holds (all goals proved). */

int secret = 0;   /* the confidential region — never read here */
int a = 0;
int b = 0;

/*@ happy \prop,
      \name("noread"),
      \targets(\ALL),
      \context(\reading),
      \separated(\read, &secret);
*/

void compute(void)
{
  b = a;            /* reads a -> \separated(&a, &secret) holds */
  a = b + 1;        /* reads b -> \separated(&b, &secret) holds */
}
