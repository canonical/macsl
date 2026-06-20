/* H-I2 positive control: noninterference via self-composition.
   `check`'s result depends only on the PUBLIC input `attempt`, not on the
   SECRET `stored`. macsl synthesizes check__selfcomp (two calls: shared
   attempt, distinct stored_a/stored_b) and asserts the results are equal;
   WP proves it from check's functional contract. */

/*@ assigns \nothing; ensures \result == attempt; */
int check(int attempt, int stored);

/*@ happy \prop,
      \name("noleak"),
      \targets({check}),
      \context(\noninterference),
      \secret(stored);
*/
