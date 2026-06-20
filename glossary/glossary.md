# macsl / HAPPY glossary

Terms used by macsl and its documents. ACSL/Frama-C terms are defined only as macsl uses them; see the
Frama-C and ACSL manuals for their full meaning.

### HAPPY
**Hyperproperty Analysis for Program PolicY** — the policy framework macsl implements. The rename and
re-scope of MetAcsl's **HILARE**. A HAPPY policy states a global property once; macsl expands it into
per-site assertions. Long-term, HAPPY aims at one property family per STRIDE category
(`../happy-roadmap.md`); Phase 0 delivers write confinement.

### HILARE
MetAcsl's name for its meta-property mechanism. macsl renames it HAPPY (and keeps the surface
compatible). Not "broken" — see [design.md](../docs/design.md) §1.

### meta-property / policy
A global, module-level declaration that ranges over many program points, as opposed to a per-function
contract. In macsl, written with the `happy` ACSL extension keyword. (MetAcsl uses `meta`.)

### context (`\writing`, `\reading`)
The class of program points a policy ranges over. Implemented: `\writing` — every memory **write** in
the target functions (H-T); `\reading` — every memory **read** (H-I1). (Roadmap: `\calling`,
invariants.)

### meta-variable (`\written`, `\read`, …)
A placeholder in the policy predicate that is bound to the concrete site at instrumentation time. In
the `\writing` context, `\written` is the **address of the written lvalue** (`&x` for `x = …;`) and
`\lhost_written` the address of its base. In the `\reading` context, `\read` is the **address of the
read lvalue** and `\lhost_read` its base. `\called` is reserved for the future `\calling` context.

### read site
An occurrence of an lvalue in a **read** position: any lvalue inside an expression — a right-hand side,
a condition, a call argument or callee, a return value, or an offset index. *Not* a write-target lval
(that is a write site) and *not* an address-taken lval (`&x` does not read `x`'s value). macsl emits
one read-separation assert per distinct read lvalue per statement.

### read confinement (H-I1)
The Phase-1 property: "no targeted function **reads** region *R*", expressed as
`\separated(\read, R)`. The mirror of write confinement. STRIDE **Information disclosure** (partial) —
code **H-I1**. **Not** noninterference: it proves the secret is not *read* outside the enclave, not
that exempt readers' outputs are independent of it (that is **H-I2**, relational/self-composition).

### target (`\targets`)
The functions a policy applies to: `\targets(\ALL)` (every defined function) or `\targets({f, g})`.

### write site
A statement that writes memory: a CIL `Set`, a `Call` with a result lvalue, or a `Local_init`. macsl
emits one assertion per write site in each target function.

### write confinement / isolation
The Phase-0 property: "no targeted function writes region *R*", expressed as
`\separated(\written, R)`. macsl emits this separation assert at each write site; a site that does
write *R* yields `\separated(&R, R)`, which is false, so WP cannot prove it. This is STRIDE
**Tampering** (integrity) — code **H-T** in the roadmap.

### separation (`\separated`)
The ACSL predicate that two memory locations do not overlap. macsl builds `\separated(\written, R)`
per site. `\separated(&secret, &secret)` is **false** (a location overlaps itself) — the mechanism by
which a forbidden write is caught.

### in-place instrumentation
macsl adds the generated asserts to the **current** project's AST (no project copy), via
`Ast.apply_after_computed` + `Annotations.add_code_annot`. This is the design choice that lets
`frama-c file.c -macsl -wp` work in one stage. Contrast: MetAcsl builds a **copy** project and needs
`-then-last`.

### the `-then-last` footgun
MetAcsl's instrumented AST lives in a separate project, reached only with `-then-last`, and the input
file must reach the `-meta` stage. Getting either wrong yields a silent vacuous pass — the trap that
caused macsl's original (mistaken) "no-op" diagnosis. macsl removes it by instrumenting in place.

### add-only / faithfulness
macsl only *adds* `assert` annotations; stripping them recovers byte-identical source. No code is
rewritten. The same discipline as the surrounding verification work.

### non-vacuity gate
The rule that a green result is admissible only if (a) instrumentation is **visible**
(`-macsl-print` shows the asserts) and (b) a **negative control** — a deliberately violating site —
is genuinely **unproved**. A policy expanding to zero asserts is not a pass.

### zero-expansion warning
The diagnostic macsl emits when a policy matches no site (`-macsl-warn-key zero-expansion=abort` to
make it fatal). Guards against "succeeded but checked nothing."

### negative control
A test (`writing_neg.c`) with a site that violates the policy; its generated assert must be **red**
(unproved by WP) for the policy to have "teeth." Required before trusting any green.

### emitter
The Frama-C `Emitter.t` that attributes the generated assertions (and their statuses) to macsl,
distinguishing them from user annotations and other plugins' output.

### delayed typing / `p_property` closure
The policy predicate is stored untyped and re-type-checked at **each** write site with the
meta-variable bound to that site (`p_property : kf -> substitution -> predicate`). This is how one
written policy yields a correctly-typed assert at every site.

### Phase 0 / Phase 1 / milestone M0
Phase 0 = the `\writing` write-confinement checker (H-T); Phase 1 = the `\reading` read-confinement
checker (H-I1) — both in this repo, working and tested. M0 = "run MetAcsl's own test", the step that
corrected the no-op misdiagnosis before any code was written.

### STRIDE (H-T … H-I2)
The threat taxonomy (Spoofing, Tampering, Repudiation, Information disclosure, Denial of service,
Elevation of privilege). HAPPY's roadmap maps one property family to each; the codes `H-T … H-I2` are
defined in `../happy-roadmap.md`. Implemented so far: **H-T** (Tampering / write confinement) and
**H-I1** (Information disclosure, first half / read confinement).
