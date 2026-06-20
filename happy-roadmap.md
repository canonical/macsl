# HAPPY Roadmap (C / ACSL) — From Write Integrity to Full STRIDE Coverage

**HAPPY** = **Hyperproperty Analysis for Program PolicY** — the `macsl` meta-property framework
(the rename + rescope of MetAcsl's HILARE; see `../macsl.md`).

**Status:** Roadmap — pre-normative. Each milestone graduates to Normative only when its directive
surface lands in the `macsl` annotation reference, its lowering (the §T "how it becomes asserts +
WP VCs" rules) is written, a prove/fail ptests pair ships under `tests/`, and the cross-reference +
non-vacuity gates pass for the new directives. Until then, every syntax sketch here is a design
proposal, not an accepted ACSL/`happy` production.
**Version:** 0.1
**Source of truth:** the Phase-0 `macsl` meta-pass specified in `../macsl.md` (the spec) and
`macsl-impl.md` (the implementation): the `\writing`/`\reading`/`\calling` contexts, `\separated`
isolation predicates, and the `\fguard`/`\tguard` guards, instrumented **in place** on the CIL AST and
discharged by WP. Cross-referenced against the verdict/soundness discipline of the `frama-c-monitoring`
skill (the depth ladder, the non-vacuity gate, the soft-residual) and the STRIDE taxonomy of the
`stride` skill.
**Scope:** the extension of the `happy` meta-property language to express and discharge **one property
family per STRIDE category**. It does NOT cover the EBIOS-RM risk gate that consumes these properties
(see the `ebios-risk-manager` / `ebios-sl` skills and `frama-c-launch`'s `ebios-feedback`), and it does
NOT restate WP's VC-generation rules — each milestone that ships must add its own §T lowering section.
**Companion documents:** `../macsl.md` §5 (semantic model) and §7 (the STRIDE↔HAPPY table);
`macsl-impl.md` (in-place instrumentation, emission via `Annotations.add_code_annot`); the `frama-c`
skill (ACSL authoring, RTE/UB); the `frama-c-monitoring` skill (verdict discipline, the Coq escalation
route on the `framac-coq8` switch); the `ebios-risk-manager` skill (the residual-risk register these
properties feed).

---

## 0. Where HAPPY stands, stated in the exact machinery

A shipped HAPPY (Phase 0: `\context(\writing)` + `\separated(\written, R)` + `\fguard`) is a global
ACSL annotation that a **meta-pass** expands **before WP runs**: at every write site touching the
protected region in a non-exempt function, the pass injects a per-site `/*@ assert <name>: meta: … */`
(via `Annotations.add_code_annot` under the `macsl` `Emitter`), instrumenting the current project's AST
**in place** — no project copy (this is what removes MetAcsl's `-then-last`/file-position footgun; see
`docs/design.md` §1–2). WP's weakest-precondition calculus (Why3 backend) turns each injected assert into a verification
condition; Alt-Ergo (then Z3) discharges it, escalating to **interactive Coq** on the `framac-coq8`
switch for goals SMT cannot close, reporting *Valid* when the goal's negation is unsatisfiable. A
trusted boundary — a **declaration-only function** (`GFunDecl`: contract, no body, **no VC of its
own**, WP assumes its `ensures`) — carries the *assumed* clause instead of a proof; that assumption
enters the trusted computing base and surfaces as **Confinement** in the soundness classification (§8),
which is what the EBIOS W5 residual-risk register consumes.

That is one STRIDE letter: **Tampering**. The proof obligation is "no unauthorized write", the
enforcement point is syntactic (every write site), and the cost model is favorable — injected checks
are ground assertions, so the dominant SMT cost is linear arithmetic over indices/addresses, not
E-matching. The roadmap below extends HAPPY to the remaining five letters in order of **mechanism
reuse**: each milestone composes machinery the verifier already has (ghost state, quantified `ensures`,
`assigns` frames, the RTE/UB alarm set, `loop variant`s, Coq-proved-and-cited `lemma`s) before any
milestone that needs genuinely new WP plumbing. The codes `H-T`, `H-I1`, `H-R`, `H-D`, `H-E`, `H-S`,
`H-I2` are intended as stable taxonomy, in the manner of the RTE/UB alarm classes.

| Code | STRIDE letter | Property family | New machinery required | `macsl` phase (§7) |
|------|---------------|-----------------|------------------------|--------------------|
| H-T  | Tampering | write confinement | none — **shipped (Phase 0)** | 0 |
| H-I1 | Information disclosure (first half) | read confinement | none — symmetric `\reading` pass — **shipped (Phase 1)** | 0–1 |
| H-R  | Repudiation | audit-log completeness + append-only | `\postcond` ensures (user-supplied ghost log) — **shipped (Phase 2)** | 1 |
| H-D  | Denial of service | totality + bounded work | RTE bundle + ghost fuel counter | 1–2 |
| H-E  | Elevation of privilege | privilege monotonicity | `\postcond` monotonicity + `\diff` gate exemption — **shipped (Phase 3)** | 1–2 |
| H-S  | Spoofing | check-before-use capabilities | `\precond` capability + WP's automatic call-site check — **shipped (Phase 4)** | 2 |
| H-I2 | Information disclosure (second half) | noninterference | relational VCs (self-composition) | 2+ |

---

## 1. H-T — Tampering (shipped target; hardening only)

Nothing new to design — H-T *is* Phase 0. Two hardening items keep the foundation honest, and both are
sharper in C than in Python because of **pointer aliasing**:

1. **Aliasing completeness.** In C a protected base can escape the meta-pass's sight through a pointer
   copy (`char *p = reserved; p[i] = v;`) or a cast (`*(int*)alias = v;`). The meta-pass matches
   *syntactic* write sites (`Set`/`Call`-with-lval/`Local_init`); the separation predicate `\separated`
   then makes WP discharge the obligation *under the memory model*. The guarantee is therefore only as
   strong as the WP memory model in force — a `char*`/union cast can defeat region separation (cf. the
   `wp-cast-frame-defect` finding). **Rule:** an H-T HAPPY must declare its memory-model assumption,
   and any cast crossing the protected base is a soundness boundary, not a silent pass (GH6).
2. **The `\fguard` escape is an assumption, not a proof.** Exempting the trusted writers
   (`\fguard({write_inode, write_dir}, \true)`) transfers the obligation to those functions' own
   contracts; a weak contract on an exempt writer is a residual attack path. Every exemption is an
   EBIOS residual-risk entry, never a silent pass — the rule every milestone below inherits.

Surface (consistent with `../macsl.md` §4):
```c
/*@ happy region_integrity:
      \targets(\ALL),
      \context(\writing),
      \fguard({write_inode, write_dir}, \true),   // only these may touch the reserved region
      \separated(\written, reserved + (0 .. RESERVED_SZ - 1));
*/
```
**Flagship use case:** a reserved on-disk/metadata region (the inode-filesystem model, or a heap
allocator's bookkeeping block) only the owner functions may write; a formatter bug writing at the wrong
offset fails at its own site, with the HAPPY and the site named in the WP diagnostic. This is the
`monotony.c`-class regression that must go **red** (the Phase-0 acceptance test).

---

## 2. H-I1 — Read confinement (`\reading` + `\separated(\read, R)`) — **IMPLEMENTED (Phase 1)**

The cheapest extension, because it is the mirror of H-T. **Shipped** in `src/macsl.ml`
(`reading_visitor`) and tested (`tests/phase1/reading_{pos,neg}.c`, `3/4` vs `4/4`). Surface:
```c
/*@ happy key_confidentiality:
      \targets(\ALL),
      \context(\reading),
      \fguard({kdf, sign}, \true),
      \separated(\read, disk + (0 .. 63));
*/
```
The meta-pass walks **read sites** (`Lval` in `exp`s, reads feeding calls) instead of write sites and
injects the same ground `\separated(\read, R)` before each, in every non-exempt function. Lowering, VC
shape, SMT cost, and the declaration-only-boundary obligation are the H-T ones with the access
direction flipped. **What this is:** a proof that no non-exempt code path *syntactically reads* the
secret bytes. **What it is NOT:** noninterference — it says nothing about what the *exempt* readers do
with the secret downstream. That stronger property is H-I2; conflating them is exactly the
"coherent-and-wrong" failure the discipline forbids.

**Flagship use case:** a private key in `disk[0..63]`. The error-message formatter — the classic leak
channel — must verify with zero failing read-checks, proving it cannot have read key bytes into the
string it builds. A negative driver (formatter peeks at `disk[3]`) must fail at the read site.

---

## 3. H-R — Repudiation (audit-log completeness + append-only) — **IMPLEMENTED (Phase 2)**

Non-repudiation, at the level a deductive verifier can honestly claim, is a **completeness and
immutability theorem about a log**: every protected state change produces a record, and no path can
rewrite history.

**Shipped realization (the lean version).** macsl implements this through the **`\postcond` context**:
the user supplies the ghost log and the append code, and macsl injects the obligation as a *checked
postcondition* on each target function. Surface (tested in `tests/phase2/`):
```c
//@ ghost int log_len = 0;                  // the user's ghost log (length here; + an array for append-only)
/*@ happy \prop, \name("audit"), \targets(\ALL), \context(\postcond),
      \old(disk) != disk ==> log_len > \old(log_len);                       // completeness
*/
/*@ happy \prop, \name("immut"), \targets(\ALL), \context(\postcond),
      \forall integer i; 0 <= i < \old(log_len) ==> logbuf[i] == \old(logbuf[i]);  // append-only
*/
```
`emit_ensures` types each predicate in the post-state and adds it via
`Annotations.add_ensures kf [(Normal, new_predicate ~kind:Check P)]`. WP discharges it:
`audit_pos.c`/`immut_pos.c` prove (`3/3`); `audit_neg.c` (an unlink that forgets to log) and
`immut_neg.c` (a rewrite of `logbuf[0]`) leave the postcondition **red** (`2/3`).

**Deferred sugar (the heavy version).** A dedicated `\audit(state, log)` directive that
*auto-declares* the ghost log and *auto-injects* the append at each write site (so the user writes
neither) is still future work; the manual ghost-log + `\postcond` form above already delivers the
completeness + immutability theorem. The append-only `\forall` is quantified, so on larger logs the
dominant cost is E-matching on the prefix instantiations; the prefix lemma is then a candidate for the
**Coq route** — proved once offline on `framac-coq8` as an ACSL `lemma`/`axiomatic`, replayed and
cached (`-wp-cache`), instantiated as an in-scope assumption (cf. `wp-interactive-coq-replay`).

**What this is NOT:** cryptographic non-repudiation. The verifier proves the *program* cannot skip or
rewrite a record; that the log survives on storage, is signed, and binds an identity stays a trusted
boundary EBIOS must carry (GH1).

**Flagship use case:** `sys_write` and `sys_unlink` each provably append exactly one record; a negative
driver whose "optimized" unlink skips logging fails its completeness `ensures`. "Show me the deletion
that left no trace" becomes a VC Alt-Ergo refutes.

---

## 4. H-D — Denial of service (totality + bounded work)

Frama-C already owns every ingredient: `loop variant` (and a function `terminates` clause) makes
termination a WP sub-goal; **`-wp-rte`** turns the C undefined-behavior set into per-operation
assertions (no integer overflow, no out-of-bounds, no null deref, no division by zero) — the C analog
of "no uncaught exception"; integer bounds are VCs under the WP arithmetic model. H-D is therefore a
**bundling** HAPPY plus one new ghost:
```c
/*@ happy request_availability:
      \total({parse_request, dispatch}),     // pre-normative bundle, see lowering
      \fuel(4 * len);
*/
```
`\total f` is a hard meta-pass error unless `f` (and transitively every loop in it) carries a variant
**and** `-wp-rte` discharges every injected RTE assert — i.e., the bundle makes "this function returns
normally and faults on **no** input" a checked claim instead of a convention. `\fuel` injects a ghost
step counter incremented in each loop body, with the bound carried as an injected loop invariant; the
closing VC proves the counter never exceeds the declared expression. **State the strength precisely**
(EBIOS consumers will over-read it): this proves **totality + an iteration bound over the WP-modelled
loops** — the never-faults / always-returns theorem — **not** wall-clock complexity, **not** `malloc`
/ OS / allocator behaviour. Those stay attack paths in the risk study (GH2).

**Flagship use case:** a request parser over attacker-controlled bytes. The historical DoS pattern —
a crafted length field driving a `while` past any bound, or a malformed packet indexing out of bounds —
becomes two failing VCs (variant decrease; the `-wp-rte` bounds assert) on the negative driver and a
*Valid* verdict on the fixed one, for **every** input the quantified VC ranges over, not the sampled
few a fuzzer reaches.

---

## 5. H-E — Elevation of privilege (privilege monotonicity) — **IMPLEMENTED (Phase 3)**

`\writing` confinement prevents a non-owner from writing privileged state *directly*; the deliberate
gap is that it allows going *through the API*. H-E closes the gap above the API by making the
**privilege level itself** subject to a monotonicity law: outside the gate, privilege may only stay or
descend.

**Shipped realization.** macsl realizes this as a `\postcond` monotonicity obligation over a target set
that excludes the gate via `\diff` (tested in `tests/phase3/`):
```c
int proc_priv = 0;   // 0 = user, 1 = admin
/*@ happy \prop, \name("noesc"),
      \targets(\diff(\ALL, {sudo_gate})),   // the gate is exempt; it may raise
      \context(\postcond),
      proc_priv <= \old(proc_priv);          // everyone else may only keep or lower privilege
*/
```
WP discharges it: `priv_pos.c` proves `8/8` (the gate carries no obligation; `do_work`/`drop` satisfy
monotonicity); `priv_neg.c`'s confused-deputy `escalate` leaves its monotonicity postcondition **red**
(`4/5`). The lattice order over more than two levels is a small finite **`axiomatic`** block (or a
Coq-proved order lemma), or simply integer-encoded as above. `sudo_gate`'s own contract — the condition
under which it may raise — is what **H-S** supplies.

**Deferred:** the `\privilege(...)/\raises_only_in(...)` sugar and the direct-write-confinement piece
(H-T on the privilege field with `\fguard({sudo_gate})`) — the latter waits on `\fguard`. The
monotonicity law above is the stronger, API-spanning part and already catches the confused deputy.

**Flagship use case:** filesystem permission bits. `sys_chmod` running as `user` must be unable —
through *any* call path, including ones routed through owner functions — to end a call with
`proc.priv == admin`. The negative driver is the classic confused-deputy: a helper reachable from
unprivileged code that writes the privilege field "temporarily"; it fails the monotonicity `ensures` at
the helper, naming the HAPPY and the site.

---

## 6. H-S — Spoofing (check-before-use capabilities) — **IMPLEMENTED (Phase 4)**

Spoofing defenses ultimately rest on a cryptographic/external identity check a WP verifier cannot and
should not pretend to prove — `verify_token` is a **declaration-only function** with a trusted, cited
contract. What the verifier **can** prove, for all inputs and paths, is the *discipline* around it: no
protected operation is reachable without the check having succeeded.

**Shipped realization.** macsl realizes this with the **`\precond` context** (tested in
`tests/phase4/`):
```c
//@ ghost int session_ok = 0;
/*@ assigns session_ok; ensures \result != 0 ==> session_ok == 1; */
int verify_token(int tok);                    // trusted, declaration-only

/*@ happy \prop, \name("authn"),
      \targets({sys_write, sys_unlink, sys_chmod}),   // the guarded ops
      \context(\precond),
      session_ok == 1;
*/
```
`emit_requires` injects `requires session_ok == 1` on each guarded function. **The load-bearing check
is automatic:** WP enforces a callee's precondition at every call site, so an unauthenticated path to a
guarded op fails *in the caller* — no separate call-site `assert` emission is needed. Verified:
`authn_pos.c` (caller checks the token first) proves `5/5`; `authn_neg.c`'s `maintenance` (direct call)
leaves `…_call_sys_write_requires_authn_meta` **red** (`4/5`). `verify_token` stays the trusted
boundary (the EBIOS assumption "token verification is correct"); everything around it is Modelled. To
also confine *who may grant* the capability, add an H-T policy `\separated(\written, &session_ok)` over
`\diff(\ALL, {verify_token})`.

**Flagship use case:** a session layer over the filesystem model. The negative driver is the
forgotten-check bug — a new maintenance endpoint calling `sys_unlink` directly; the injected call-site
check yields an unprovable VC the moment the file is verified, before review, before deployment. The
positive driver shows the full chain *Valid*: `verify_token` (trusted contract) → capability ghost →
guarded syscall.

---

## 7. H-I2 — Noninterference (the one genuinely new mechanism)

H-I1 proves secrets are not *read* outside the enclave; H-I2 proves the enclave's **outputs do not
depend on them** — noninterference with declassification. This is the only milestone that cannot be
assembled from per-site checks and injected `ensures`, because the property is **relational**: it
compares two executions. The standard WP-supported reduction is **self-composition** — analyze the
function over two disjoint copies of the store, equate the low-labelled inputs in the `requires`, and
assert equality of low-labelled outputs in the `ensures`. WP then produces ordinary first-order VCs,
but over a doubled state, so E-matching cost grows sharply with function size. (Prior art in the
Frama-C ecosystem: the relational-property / self-composition line of work — *RPP*; H-I2 should reuse a
proven encoding rather than invent one.) The engineering substance is keeping the composed VC
affordable: modular contract boundaries so each function's relational proof is done once and reused via
its contract, and ground unrolling over fixed-size buffers instead of quantifiers. Proposed surface:
```c
/*@ happy no_leak:
      \secret(disk + (0 .. 63)),     // pre-normative relational labels
      \public(\result, net_out),
      \declassify(sign);
*/
```
**What this is NOT:** a side-channel proof. Timing, cache, and allocation behaviour are below the WP
memory model; EBIOS keeps them (GH3). **Sequencing:** H-I2 is deliberately last — it lands only after
H-I1's labels and enclave syntax are stable, so the relational pass reuses the same declarations rather
than inventing a second labelling language.

**Flagship use case:** the login path. `check_password(stored, attempt)` must return a result whose
*value* is the only thing depending on the secret — the composed VC proves two runs with different
`stored` but equal `attempt` produce equal observable output apart from the declassified boolean. The
negative driver returns early with a length-dependent error; the relational postcondition fails — the
verified version of the oldest password-oracle bug in the book.

---

## 8. Cross-cutting obligations (every milestone, no exceptions)

Each milestone ships only with: its `happy` grammar/surface in the `macsl` annotation reference;
well-formedness rules + plugin error codes (the static checks in `macsl_parse`); lowering rules (a §T
section in `macsl-impl.md` or its successor); a canonical-directive entry with oracle in `tests/`; a
**prove/fail ptests pair** in the pattern of `writing_pos.c`/`writing_neg.c` (the mandatory negative
control); and a clean cross-reference + **non-vacuity** gate (`-macsl-print` shows the generated
asserts, `-macsl-list-targets` counts them, a zero-expansion policy aborts, and the `_neg` obligation
goes red). Each escape hatch — a `\fguard` exemption, a `\declassify`, a trusted declaration-only
contract — must be **classified by the soundness report and routed into the EBIOS W5 residual-risk
register mechanically**, not by memory.

The soundness classification (the `--soundness-report` analog, grounded in `Property_status` +
the squeeze-loop verdicts):
- **Modelled** — full body, every injected obligation WP-discharged (and non-vacuous).
- **Specified / Assumed** — a declaration-only contract WP assumes (no VC); trusted boundary.
- **Stubbed** — a body abstracted away for the proof.
- **Confinement** — an obligation transferred out of scope by `\fguard`/exemption.

A milestone whose checks pass but whose exemptions are **invisible** to the soundness report — and thus
to the EBIOS residual-risk register — is **not done**. (This is the macsl realization of the
soft-residual: the bounded set of clauses a human must adjudicate.)

---

## 9. Gap analysis

- **GH1 — Spoofing/Repudiation are discipline proofs, not identity proofs.** H-S and H-R prove the
  program enforces check-before-use and log-completeness; the identity check (`verify_token`) and the
  log's external integrity are trusted declaration-only contracts. Permanent boundary, by design.
- **GH2 — H-D bounds modelled work only.** Iteration counts over WP-modelled loops; no claim about
  `malloc`/OS/allocator behaviour or wall-clock; WP termination is partial (recursion/`terminates`
  must be stated).
- **GH3 — H-I2 excludes side channels.** Timing, cache, and allocation are below the memory model; out
  of scope for any milestone here.
- **GH4 — Concurrency unspecified.** WP's memory model is sequential; the composition of every H-x with
  threaded C (data races, critical sections) is undesigned — until specified, security HAPPYs are sound
  only under the sequential assumption.
- **GH5 — Exempt-function behaviour.** Every `\fguard`/exemption transfers the obligation to the exempt
  function's own contract; a weak contract on an exempt writer/reader is the residual attack path EBIOS
  must rate (GH1's general form).
- **GH6 — Memory-model / aliasing soundness (C-specific).** Region separation (`\separated`) is only as
  strong as the active WP memory model; `char*`/union casts and out-of-model pointer arithmetic can
  defeat it (cf. `wp-cast-frame-defect`). Every region/secret HAPPY must declare its memory-model
  assumption, and a cast crossing a protected base is a soundness boundary, not a silent pass. This gap
  has no Python analog and gates H-T, H-I1, and H-I2.
```
