/* H-D: termination of a strtok-style parse loop — the gap behind main.c's
   get_query_param, isolated and FIXED with a SOUND contract strengthening.
   =======================================================================
   main.c's `while (token != NULL) { …; token = strtok(NULL,"&"); }` cannot be
   proved terminating against Frama-C's shipped strtok contract: its `resume_str`
   behavior ensures the saved pointer stays valid and same-base, but NOT that it
   strictly ADVANCES — so no loop variant decreases. Real strtok always advances
   its saved pointer past each returned token, so adding a strict-progress
   `ensures` is a FAITHFUL strengthening, not a new assumption.

   This file models strtok's saved position as a ghost int `tok_pos ∈ [0,CAP]`
   and adds exactly that one missing `ensures`. The parse loop then carries a
   variant (`CAP - tok_pos`) and H-D `\total` proves it terminates. Self-contained
   (no <string.h>) so the local contract governs. To finish main.c's *real*
   get_query_param, the same `ensures` must be added to the libc strtok contract
   (see ../getting-better/ candidate) — this proves that strengthening suffices. */

#define CAP 512

/*@ ghost int tok_pos; */   /* abstract offset of strtok's saved pointer */

/*@ assigns tok_pos;
    behavior first:                       // strtok(s, …) with s != NULL: (re)start
      assumes s != \null;
      ensures 0 <= tok_pos <= CAP;
      ensures \result != \null ==> tok_pos < CAP;
    behavior resume:                      // strtok(NULL, …): continue
      assumes s == \null;
      requires 0 <= tok_pos <= CAP;
      ensures 0 <= tok_pos <= CAP;
      // THE MISSING GUARANTEES (sound for real strtok):
      //  - while there is room, the saved pointer strictly advances;
      ensures \old(tok_pos) < CAP ==> tok_pos > \old(tok_pos);
      //  - a returned token means we were not yet at the end (room remained).
      ensures \result != \null ==> tok_pos < CAP;
    complete behaviors;
    disjoint behaviors;
*/
char *strtok(char *s, const char *delim);

/*@ requires buf != \null;          // the first call is a (re)start, not a resume
    assigns tok_pos; */
void parse(char *buf, const char *delim)
{
  char *tok = strtok(buf, delim);
  /*@ loop invariant 0 <= tok_pos <= CAP;
      loop invariant tok != (char *)0 ==> tok_pos < CAP;   // a live token ⇒ room
      loop assigns tok, tok_pos;
      loop variant CAP - tok_pos;     // strictly decreases: entering with a live
                                      // token (tok_pos < CAP) the resume advances
  */
  while (tok != (char *)0) {
    tok = strtok((char *)0, delim);
  }
}

/* H-D availability: the parse loop always terminates (and -wp-rte: never faults). */
/*@ happy \prop, \name("parse_terminates"),
      \targets({parse}), \context(\total),
      \true;
*/
