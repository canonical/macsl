# EBIOS RM report — Mbed TLS 4.1.0

*Method: ANSSI EBIOS Risk Manager (© ANSSI, Open Licence Etalab v1). This study was authored
code-blind: workshops W1–W4 were written from the public mission and threat model of Mbed TLS only,
without reading the implementation source. The study is the exogenous upper bound that a downstream
Frama-C verification campaign consumes as its risk ranking.*

**Studied object.** Mbed TLS 4.1.0 — a small, portable, standards-compliant library implementing
TLS and DTLS, X.509 certificate handling, and the underlying cryptographic primitives. It is the
network-security boundary on IoT and constrained devices as well as on servers and gateways. By
mission it processes attacker-controlled bytes at every protocol layer: the moment a peer connects,
untrusted input flows through the record layer, the handshake state machine, the certificate parser,
and the cryptographic core.

**Goal & workshop subset.** Complete, fine risk study to drive formal verification: W1, W2, W3, W4
authored here; W5 (residual-risk treatment and sign-off) is fed downstream and adjudicated by the
risk owner — see the Provenance & assurance status section.

**Cycles.** Strategic cycle 3 years; operational cycle 1 year.

**Trusted security baseline (compliance approach — out of deliberate-attacker scope).** Per EBIOS
doctrine the baseline absorbs accidental and environmental risk and the assumed-hard foundations, so
the scenario workshops can concentrate on the intentional attacker. The baseline trusts: (1) the
mathematical hardness of the standard primitives themselves (the difficulty of breaking AES, the
SHA-2 and SHA-3 families, RSA, and the elliptic-curve discrete-log problem when used at adequate
sizes) — cryptanalysis of a correctly-sized standard primitive is assumed infeasible and is NOT a
deliberate scenario; (2) accidental faults — power loss, cosmic-ray bit flips, disk corruption, and
operator misconfiguration of the surrounding application; (3) physical and supply-chain integrity of
the build and the host platform; (4) correct use of the public interface by the embedding
application (the application authenticates the right way and checks return codes); (5) basic platform
hygiene — memory protection, current toolchain, secure-boot where available. Everything below the
baseline is what the deliberate, remote, byte-injecting attacker can still do.

## Workshop 1 — Scope & Security Baseline

**Business assets (the value the library exists to protect).**

- BA1 Confidentiality of the protected channel — application data carried over TLS or DTLS stays secret from any party other than the two endpoints.
- BA2 Integrity and authenticity of the protected channel — data received is exactly what the authenticated peer sent, with no tampering, reordering, replay, or injection.
- BA3 Endpoint authentication — each side is cryptographically assured of the identity of the peer it is talking to, so it is not talking to an impostor.
- BA4 Long-term private keys and session secrets — server and client private keys, pre-shared keys, and per-session traffic secrets used to key the channel.
- BA5 Availability of the secured service — the ability of an endpoint to keep establishing and serving secured connections to legitimate peers.
- BA6 Trust-decision correctness — the verdict the library returns about whether a peer's certificate chain is valid and trusted, on which the application bets its security.
- BA7 Forward secrecy of past sessions — recorded past traffic stays secret even if a long-term key is later compromised.
- BA8 Memory safety of the security boundary — the property that processing hostile input never corrupts the host process, which would otherwise convert a network message into host control.

**Supporting assets (named by ROLE only — the components that bear the business assets).**

- SA1 X.509 and ASN.1/DER certificate parser — decodes attacker-supplied certificate bytes into structured fields.
- SA2 Certificate-chain and path-validation engine — builds and verifies the chain to a trust anchor, applying name, validity-period, key-usage, and basic-constraints rules.
- SA3 TLS/DTLS handshake state machine — drives the ordered exchange of handshake messages and negotiates version, cipher suite, and key-exchange parameters.
- SA4 Record-layer and AEAD/decryption engine — frames, encrypts, decrypts, and authenticates record payloads, including any padding removal.
- SA5 Random and entropy subsystem — gathers entropy and produces the random values used for keys, nonces, and protocol randoms.
- SA6 Cryptographic primitive core — the symmetric, hash, public-key, and key-derivation routines invoked by the protocol layers.
- SA7 Session-resumption and ticket subsystem — stores, issues, and reloads resumption state so a returning peer can shortcut a full handshake.
- SA8 Protocol-version and cipher-suite negotiation logic — selects the agreed version and algorithms from each side's offered set.
- SA9 Key-exchange and signature-verification logic — performs the key-agreement and verifies the peer's handshake signatures.

**Feared events (with severity G1 minor, G2 significant, G3 serious, G4 critical).**

- FE1 Remote code execution or memory corruption in the host process triggered by hostile certificate or protocol input — severity G4 (impacts BA8, BA4)
- FE2 An impostor is accepted as the authenticated peer because chain or path validation returns trusted for an untrusted certificate — severity G4 (impacts BA3, BA6)
- FE3 Confidentiality of application data is broken so an eavesdropper or man-in-the-middle reads protected traffic — severity G4 (impacts BA1)
- FE4 Long-term private keys or session secrets are extracted by the attacker — severity G4 (impacts BA4, BA7)
- FE5 Integrity of the channel is broken so an attacker injects, tampers with, or replays application records undetected — severity G3 (impacts BA2)
- FE6 The secured service is rendered unavailable to legitimate peers by remote input — severity G3 (impacts BA5)
- FE7 The negotiated protection is silently downgraded to a weak version, cipher, or key strength below policy — severity G3 (impacts BA1, BA2, BA3)
- FE8 Forward secrecy is lost so recorded past sessions become decryptable after a later key compromise — severity G3 (impacts BA7)
- FE9 Information about secret-dependent internal state leaks through timing, error, or behavioural side channels usable as an oracle — severity G3 (impacts BA1, BA4)
- FE10 Predictable or low-entropy random output weakens keys, nonces, or protocol randoms — severity G4 (impacts BA4, BA1, BA7)

## Workshop 2 — Risk Origins (RO/TO)

- RO1 / TO1: A network-positioned cybercriminal or opportunistic attacker seeking to break into or steal data from any reachable endpoint at scale, for fraud or resale.
- RO2 / TO2: A man-in-the-middle adversary on the path (hostile access network, rogue gateway, compromised upstream) seeking to read or alter the protected traffic of targeted victims.
- RO3 / TO3: A state-level or strategic actor seeking durable, stealthy decryption of high-value communications, including retroactive decryption of recorded traffic.
- RO4 / TO4: A hacktivist or sabotage-motivated actor seeking to take the secured service offline or degrade it to damage the operator's reputation or continuity.
- RO5 / TO5: A malicious counterparty (a peer that legitimately connects but is itself hostile) seeking to subvert the endpoint it talks to, escalate beyond its allowed role, or impersonate others.

## Workshop 3 — Strategic Scenarios (severity flows from W1 feared events)

- SS1: RO1/TO1 reaches FE1 by sending a crafted certificate or handshake message that corrupts memory in the parsing path via SA1 — severity G4 — attack path AP1
- SS2: RO5/TO5 reaches FE2 by presenting a certificate chain that passes validation despite not chaining to a trusted anchor via SA2 — severity G4 — attack path AP2
- SS3: RO2/TO2 reaches FE7 then FE3 by forcing negotiation down to a weak version or cipher via SA8, then exploiting the weakened channel — severity G3 — attack path AP3
- SS4: RO2/TO2 reaches FE9 then FE3 by exploiting a secret-dependent padding or decryption oracle in the record layer via SA4 — severity G3 — attack path AP4
- SS5: RO5/TO5 reaches FE1 or FE6 by driving the handshake into an out-of-sequence or confused state that mishandles a message via SA3 — severity G4 — attack path AP5
- SS6: RO3/TO3 reaches FE10 then FE4 by predicting or biasing random output produced by SA5 to recover keys or nonces — severity G4 — attack path AP6
- SS7: RO3/TO3 reaches FE9 then FE4 by exploiting a timing or error side channel in the key-exchange and signature path via SA9 to extract a long-term secret — severity G3 — attack path AP7
- SS8: RO5/TO5 reaches FE5 by abusing record sequencing, replay, or resumption handling to inject or replay records via SA4 and SA7 — severity G3 — attack path AP8
- SS9: RO4/TO4 reaches FE6 by sending malformed or amplification-inducing protocol input that exhausts resources via SA3 and SA4 — severity G3 — attack path AP9
- SS10: RO2/TO2 reaches FE8 by stripping or weakening forward-secret key exchange during negotiation via SA8 and SA9 — severity G3 — attack path AP10
- SS11: RO5/TO5 reaches FE4 by forging or replaying resumption tickets to recover or reuse session secrets via SA7 — severity G3 — attack path AP11

## Workshop 4 — Operational Scenarios (likelihood V1 rather unlikely, V2 likely, V3 very likely, V4 nearly certain)

- OS1: AP1 on SA1 — attacker delivers a certificate whose nested ASN.1/DER structure drives the decoder past a buffer or into an inconsistent length, corrupting host memory; reachable pre-authentication on any endpoint that parses peer certificates — covers FE1, SS1 — likelihood V3
- OS2: AP2 on SA2 — attacker submits a chain that the path-validation engine accepts as trusted despite a broken link in name matching, basic-constraints, validity period, or anchor binding, defeating endpoint authentication — covers FE2, SS2 — likelihood V2
- OS3: AP3 on SA8 — man-in-the-middle rewrites the offered version or cipher set during the negotiation interface so both sides settle on a weak suite, then attacks the weakened channel — covers FE7, FE3, SS3 — likelihood V2
- OS4: AP4 on SA4 — attacker submits chosen ciphertext records and measures the decrypt-or-pad-failure response to build a padding or decryption oracle that recovers plaintext byte by byte — covers FE9, FE3, SS4 — likelihood V2
- OS5: AP5 on SA3 — attacker sends handshake messages out of the expected order or with duplicated or skipped steps, driving the state machine into a confused state that mishandles input and corrupts memory or aborts service — covers FE1, FE6, SS5 — likelihood V2
- OS6: AP6 on SA5 — attacker exploits weak seeding or a biased generator so that keys, nonces, or protocol randoms become predictable, then reconstructs session keys — covers FE10, FE4, SS6 — likelihood V1
- OS7: AP7 on SA9 — attacker submits adaptively chosen key-exchange or signature inputs and times the response or observes distinguishable error behaviour to extract bits of a long-term private key — covers FE9, FE4, SS7 — likelihood V2
- OS8: AP8 on SA4 — attacker replays or reorders authenticated records, or abuses sequence-number and resumption handling at the record interface, to inject or replay application data undetected — covers FE5, SS8 — likelihood V2
- OS9: AP9 on SA3 — attacker floods the handshake interface with malformed or initial messages, or abuses datagram retransmission and fragmentation, to exhaust memory or amplify traffic and deny service — covers FE6, SS9 — likelihood V3
- OS10: AP10 on SA9 — man-in-the-middle steers negotiation away from ephemeral key exchange toward a non-forward-secret mode so recorded traffic stays decryptable after a later key compromise — covers FE8, SS10 — likelihood V2
- OS11: AP11 on SA7 — attacker forges, replays, or reuses a resumption ticket at the resumption interface to recover or re-establish session secrets without a fresh authenticated handshake — covers FE4, SS11 — likelihood V1
- OS12: AP2 on SA1 and SA2 — attacker chains a certificate that parses cleanly but carries field values that the validation engine misinterprets, combining a parser quirk with a path-validation gap to be accepted as trusted — covers FE2, SS2 — likelihood V2

## Provenance & assurance status (W5 — NOT authored here)

This study was developed **code-blind**: workshops W1–W4 were authored solely from the public mission
and threat model of Mbed TLS 4.1.0, with no access to the implementation source. That barrier is what
makes this report a valid *exogenous* upper bound for the downstream Frama-C verification campaign —
the scenarios reflect the threat, not the code.

**Structure, chaining, coverage, and the endogeneity tripwire are machine-checked** by
`ebios-lint.sh` (green): every feared event carries a severity; every high-severity (G3/G4) feared
event is carried into at least one downstream scenario; every strategic scenario chains to an RO/TO;
every operational scenario chains to a strategic scenario and an attack path; and no code artifacts
appear in W1–W3.

**W5 residual-risk sign-off is PENDING.** The human risk owner (Fabrice Derepas) has **not** yet
signed off on residual risk. Risk treatment, the risk-level grid (severity × likelihood), and
acceptance decisions are fed downstream from the Frama-C verification verdicts and adjudicated by the
risk owner. **No sign-off is fabricated here.**
