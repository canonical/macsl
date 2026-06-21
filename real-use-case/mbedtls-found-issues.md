# Mbed TLS 4.1.0 — Frama-C/WP findings (RTE + functional)

Verification campaign run by the `frama-c-launch` loop, consuming
[`mbedtls-ebios-report.md`](mbedtls-ebios-report.md) for the risk ranking. Overlay,
configuration, and the faithfulness baseline are in
[`mbedtls-acsl/README.md`](../../mbedtls-acsl/README.md).

- **Config:** shipped/default `mbedtls_config.h` + default `tf-psa-crypto` crypto config
  (`ASSUMPTION`: as-released profile, unmodified). machdep `gcc_x86_64`.
- **Toolchain:** Frama-C 32.1, WP, Alt-Ergo 2.6.3 + Z3 4.13.3 (Coq 8.20.1 available), switch
  `framac-coq8`.
- **Mode:** `-wp -wp-rte` on the **as-shipped source** (no ACSL contracts added yet — this
  records the *raw* RTE baseline; the overlay closes the residue, see below).
- **Convention:** a WP `[Failed]` goal (SMT counter-example) is a genuine RTE-violation
  candidate (a bug); a `[Timeout]`/unproved goal is an *undischarged* obligation (typically a
  missing precondition), **not** itself a defect.

## Genuine defects found

**None.** Across every Tier-1 unit swept, the count of `[Failed]` (counter-example) goals is
**0** — no out-of-bounds access, signed-overflow, invalid pointer, or division-by-zero was
*refuted* by WP on the shipped parsers. This is consistent with the prior archived campaign
(`experiments/mbedtls/`) and with Mbed TLS's maturity; the value of the campaign is the
*proved* envelope plus the precise list of still-undischarged obligations below.

## RTE verdicts on the Tier-1 queue (SA1 — X.509/ASN.1 parsers)

Raw `-wp-rte`, `-wp-timeout` 2–10s, no added contracts. "Proved/Total" is auto-discharge by
Alt-Ergo+Z3; the remainder are `[Timeout]` memory-access / arithmetic obligations awaiting
buffer-validity preconditions (see classification).

| Unit | Scope | Proved / Total (raw) | `[Failed]` | Note |
|---|---|---|---|---|
| `tf-psa-crypto/utilities/asn1parse.c` | `mbedtls_asn1_get_len`, `_get_tag` (leaf) | **15 / 32** | 0 | the 17 unproved are all `assert rte mem_access` on `(*p)` reads |
| `tf-psa-crypto/utilities/asn1parse.c` | whole unit | **90 / 206** | 0 | 116 timeouts; same mem-access class |
| `library/x509_oid.c` | whole unit | **42 / 129** | 0 | OID table/length parsing |
| `library/x509.c` | whole unit | parses clean; whole-file raw RTE not bounded-completable | — | per-function RTE is the tractable mode (see method) |
| `library/x509_csr.c`, `library/pkcs7.c` | whole unit | parse clean (FULL profile) | — | amenable; same parser shape |

**Method note (why per-function, not whole-file).** Whole-file `-wp-rte` on the large X.509
units (`x509.c`, `x509_crt.c`) spawns thousands of goals and does not complete under a bounded
wall-clock; the productive mode (as in the prior campaign) is per-entrypoint
(`-wp-fct <parser>`) with the buffer-validity contract supplied. The numbers above are the
honest *raw, bounded* baseline, not a closed proof.

## Classification of the undischarged goals (the real "issues")

All unproved goals observed fall in two classes — **none is a refuted property**:

1. **`assert rte mem_access` on parser pointer reads** (the dominant class). E.g. in
   `mbedtls_asn1_get_len`, the reads `(*p)[0]`, `(*p)[1]`, … are unproved because the
   function has **no ACSL precondition** constraining `*p`/`end`/buffer validity. These are
   discharged once the overlay adds the buffer-range contract
   (`requires \valid_read(*p); requires *p <= end; …`) — the prior campaign closed
   `asn1_get_len`/`_get_tag` to **109/109** this way (RTE-robust, with one Coq *bitmask* lemma
   for the high-bit length-decoding step; 0 admits).
2. **Length-arithmetic / shift obligations** (the `len <<= 8 | b` decode): need the same
   precondition plus the bitmask lemma; reflective-SMT times out, Coq discharges it.

**Remaining engineering (undischarged, not bugs):** supply the buffer-validity contracts for
the X.509 parser entrypoints across the Tier-1 queue and replay the bitmask lemma, to lift the
raw baseline to all-`Valid`. This is the `mbedtls-acsl/` overlay work; the asn1 leaf is the
proven template.

## Tier-2 (SA3/SA4 record-header & ciphersuite parsing) — status

`ssl_msg.c` (`ssl_parse_record_header`), `ssl_ciphersuites.c`, `mps_reader.c` are amenable on
their length/parsing paths (the AEAD/crypto bodies route into the BLOCKED crypto layer). Not
swept in this bounded run; recorded as the next queue. The over-read class on the record-length
path is the FE-relevant target (EBIOS FE6/FE13 memory-safety step).

## BLOCKED surface (no RTE/functional verdict — residual risk)

See [`mbedtls-ebios-gaps.md`](mbedtls-ebios-gaps.md) for the residual-risk register: the
crypto primitive layer (SA5), RNG/entropy quality (SA6), key store/zeroization (SA9),
renegotiation logic (SA8), and supply-chain are out of WP-RTE reach and are carried as accepted
residuals pending the human risk-owner's W5 sign-off (still **pending**).
