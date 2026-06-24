/* ATT&CK: T1565.001 Stored Data Manipulation
   Negative control: `writer` writes the protected global `secret`,
   so the generated separation assertion MUST be red (unprovable). */

int secret = 0;
int pub = 0;

/*@ happy \prop,
      \name("iso"),
      \targets(\ALL),
      \context(\writing),
      \separated(\written, &secret);
*/

void writer(void)
{
  pub = 1;          /* \separated(&pub, &secret)    -> holds (green) */
  secret = 42;      /* \separated(&secret, &secret) -> FALSE (red)   */
  pub = 2;          /* holds (green) */
}
