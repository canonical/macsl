/* ATT&CK: T1040 Network Sniffing / oracle side-leak
   H-I2 negative control: a leak. `check`'s result depends on the SECRET
   `stored` (it returns attempt + stored). The synthesized self-composition's
   relational assert (ra == rb for equal public input, distinct secret) is
   unprovable -> red. This is the verified form of the oldest password-oracle
   bug: an output whose value depends on the secret. */

/*@ assigns \nothing; ensures \result == attempt + stored; */
int check(int attempt, int stored);

/*@ happy \prop,
      \name("noleak"),
      \targets({check}),
      \context(\noninterference),
      \secret(stored);
*/
