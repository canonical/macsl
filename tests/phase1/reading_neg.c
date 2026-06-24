/* ATT&CK: T1005 Data from Local System
   H-I1 negative control: `leak` READS the confidential global `secret`,
   so the generated read-separation assertion MUST be red (unprovable). */

int secret = 0;   /* the confidential region */
int pub = 0;
int sink = 0;

/*@ happy \prop,
      \name("noread"),
      \targets(\ALL),
      \context(\reading),
      \separated(\read, &secret);
*/

void leak(void)
{
  sink = pub;       /* reads pub    -> \separated(&pub, &secret)    holds (green) */
  sink = secret;    /* reads secret -> \separated(&secret, &secret) FALSE (red)   */
}
