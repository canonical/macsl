(lang dune 3.0)
(using dune_site 0.1)
(generate_opam_files true)

(package
 (name macsl)
 (synopsis "HAPPY policy checker for Frama-C (a standalone MetAcsl re-spin)")
 (description
  "macsl checks HAPPY policies (Hyperproperty Analysis for Program PolicY): a\
\n global write-confinement property stated once and instrumented at every\
\n matching write site, discharged by WP. Phase 0: the \\writing context,\
\n instrumented IN PLACE so `frama-c -macsl -wp file.c` works directly (no\
\n -then-last, no file-position footgun).")
 (depends
  (frama-c (= 32.1))))
