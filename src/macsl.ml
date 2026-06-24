(**************************************************************************)
(*  macsl — HAPPY policy checker (Hyperproperty Analysis for Program     *)
(*  PolicY).  A standalone re-spin of MetAcsl's meta-property mechanism. *)
(*                                                                        *)
(*  Phase 0: the \writing context (write confinement), instrumented      *)
(*  IN PLACE so `frama-c -macsl -wp file.c` works directly — no          *)
(*  -then-last and no file-position footgun.                             *)
(*                                                                        *)
(*  Derived from the design of MetAcsl (CEA, LGPL-2.1); same licence.    *)
(**************************************************************************)

open Logic_ptree
open Logic_typing
open Cil_types

(* ------------------------------------------------------------------ *)
(* Plugin registration + options                                       *)
(* ------------------------------------------------------------------ *)

module Self = Plugin.Register (struct
    let name = "macsl"
    let shortname = "macsl"
    let help =
      "HAPPY policy checker (write confinement); a standalone MetAcsl re-spin. \
       Instruments in place: run -wp directly, no -then-last needed."
  end)

module Enabled = Self.False (struct
    let option_name = "-macsl"
    let help = "Enable HAPPY policy checking (in-place instrumentation)"
  end)

module Number_assertions = Self.False (struct
    let option_name = "-macsl-number-assertions"
    let help = "Give each generated assertion a unique numeric suffix"
  end)

module List_targets = Self.False (struct
    let option_name = "-macsl-list-targets"
    let help = "Report, per policy, how many sites it expanded over"
  end)

module Targets = Self.String_set (struct
    let option_name = "-macsl-set"
    let arg_name = "p,..."
    let help = "Only process the named policies (default: all)"
  end)

(* A policy that matches no site is almost always a mistake (spec §8). *)
let zero_wkey = Self.register_warn_category "zero-expansion"
let () = Self.set_warn_status zero_wkey Log.Wactive

(* ------------------------------------------------------------------ *)
(* HAPPY policy representation                                          *)
(* ------------------------------------------------------------------ *)

type context =
  | Writing | Reading | Postcond | Precond | Noninterference | Total
  (* WS1 stage 1 — concurrency. [Guarded_by] walks the target's write sites and
     injects, at each one, the *checked* assertion `\held(L)` (lock L is held at
     the access).  [Stable_check] does the same with `\stable(G)` (the shared
     guard G value is stable to the act).  Both \held / \stable are
     UNINTERPRETED logic predicates — no behavioural axiom is smuggled; the
     obligation is exactly lock-held-at-access (resp. guard-stable-marker),
     nothing stronger.  See docs/usage.md "Concurrency (WS1 stage 1)". *)
  | Guarded_by | Stable_check
  (* Phase B — WS3 (M-3) principal identity.  [Authorized] walks the target's
     write sites (the H-T walk) and injects, at each protected operation, the
     *checked* assertion the policy supplies — `authorized(current_principal,
     OP)` over an UNINTERPRETED `authorized` predicate.  Where H-S/\precond only
     proved "you called the checker", this proves the principal is GENUINE: the
     literal/forged principal does not satisfy `authorized` without the binding.
     `authorized` carries NO behavioural axiom (the token check stays a trusted
     declaration-only contract).  See docs/usage.md "Principal identity (WS3)". *)
  | Authorized
  (* Phase B — WS4 (M-4) tamper-evident hash-chain log.  [Tamper_evident] emits
     `P` as a *checked* postcondition (like Postcond), where `P` is the chaining
     discipline `logbuf[i].mac == \hash(logbuf[i-1].mac, record(i))` over the
     SINGLE uninterpreted logic function `\hash` (= H).  `\hash` stays
     uninterpreted (collision-resistance is the crypto residual, NOT an axiom
     macsl smuggles); macsl proves only that every append extends the chain, so
     a splice/reorder that leaves a stale mac breaks it.  See docs/usage.md
     "Tamper-evident log (WS4)". *)
  | Tamper_evident

type target = TgAll | TgSet of string list | TgDiff of target * target

(* What a meta-variable (\written, ...) is replaced by at a site *)
type replaced_kind =
  | RepVariable of term
  | RepApp of (string * term) list

type policy = {
  p_name    : string;
  p_target  : target;
  p_context : context;
  (* the property, re-typed per site once the meta-variables are bound
     (unused for Noninterference, which carries p_secret instead) *)
  p_property : Kernel_function.t -> (string * replaced_kind) list -> predicate;
  p_secret  : string list;   (* Noninterference: the secret parameter names *)
  p_loc     : location;
}

(* Policies gathered while the ACSL extension is parsed. *)
let gathered : policy list ref = ref []

(* ------------------------------------------------------------------ *)
(* Builtin keywords so the predicate type-checks                       *)
(* ------------------------------------------------------------------ *)

(* commands/contexts are predicate builtins; meta-variables are term builtins *)
let kw_preds = [ "\\prop"; "\\writing"; "\\reading"; "\\calling";
                 "\\postcond"; "\\precond"; "\\noninterference";
                 "\\secret"; "\\public"; "\\declassify";
                 "\\weak_invariant"; "\\strong_invariant";
                 (* WS1 stage 1 concurrency markers — UNINTERPRETED predicates.
                    `\held(L)`  : lock L is held in the current state.
                    `\stable(G)`: shared guard value G is stable to the act.
                    Declared with no profile (the typer resolves them via the
                    kw_preds path in meta_type_predicate), so they carry NO
                    behavioural axiom — exactly the no-smuggled-axiom contract. *)
                 "\\held"; "\\stable";
                 (* Phase B / WS3 (M-3) — `\authorized(principal, op)`: an
                    UNINTERPRETED predicate marking "the current principal is
                    genuinely authorized for this operation".  No behavioural
                    axiom: the actual token/identity check stays a trusted
                    declaration-only contract (whoami()-style). *)
                 "\\authorized" ]
let kw_terms = [ "\\written"; "\\lhost_written"; "\\read"; "\\called" ]

(* Phase B / WS4 (M-4) — uninterpreted logic FUNCTIONS (return a term), applied
   to ordinary arguments (unlike kw_terms, which are per-site meta-variables).
   `\hash(prev_mac, record)` is the single uninterpreted hash H of the chain.
   It is declared profile-less / bodiless, so it stays uninterpreted: macsl
   emits ZERO axioms about it (collision-resistance is the crypto residual,
   supplied as a hypothesis if ever needed, never as a smuggled axiom). *)
let kw_funs = [ "\\hash" ]

let register_builtins () =
  (* Idempotent: if MetAcsl (or a previous load) already declared these
     builtins, reuse them rather than re-declaring (which is a hard error).
     This lets macsl coexist with an installed MetAcsl. *)
  let already n = Logic_env.find_all_logic_functions n <> [] in
  let mk is_pred bl_name =
    { bl_name; bl_labels = []; bl_params = []; bl_profile = [];
      bl_type = if is_pred then None else Some (Lvar "dummy") }
  in
  List.iter (fun n -> if not (already n) then Logic_builtin.register (mk true n))
    kw_preds;
  List.iter (fun n -> if not (already n) then Logic_builtin.register (mk false n))
    kw_terms;
  (* WS4: `\hash` is an uninterpreted logic FUNCTION (returns a term).  We give
     it a concrete `integer` return type (not the polymorphic `dummy`) so the
     chaining equality `mac == \hash(...)` type-checks against an integer mac.
     Still profile-less / bodiless ⇒ uninterpreted ⇒ ZERO axioms emitted. *)
  let mk_fun bl_name =
    { bl_name; bl_labels = []; bl_params = []; bl_profile = [];
      bl_type = Some Linteger }
  in
  List.iter (fun n -> if not (already n) then Logic_builtin.register (mk_fun n))
    kw_funs

(* ------------------------------------------------------------------ *)
(* Custom typing context: substitute the meta-variables               *)
(* ------------------------------------------------------------------ *)

let meta_type_predicate orig_ctxt meta_ctxt env expr =
  match expr.lexpr_node with
  | PLapp (pname, _, args) when List.mem pname kw_preds ->
    let terms = List.map (meta_ctxt.type_term meta_ctxt env) args in
    let li = List.hd (Logic_env.find_all_logic_functions pname) in
    Logic_const.papp (li, [], terms)
  | _ -> orig_ctxt.type_predicate meta_ctxt env expr

let meta_type_term termassoc orig_ctxt meta_ctxt env expr =
  match expr.lexpr_node with
  (* WS4: an uninterpreted logic function applied to ORDINARY terms (type the
     arguments through the meta context, rebuild the application against the
     builtin logic_info).  This is the term-level analog of meta_type_predicate
     for kw_preds. *)
  | PLapp (fname, _, args) when List.mem fname kw_funs ->
    let terms = List.map (meta_ctxt.type_term meta_ctxt env) args in
    (* Prefer a same-named logic function the fixture declared (without the
       backslash) — exactly the WS1 discipline where `\held` and a fixture
       `held` denote the SAME uninterpreted symbol — so the policy's `\hash`
       and the C-side trusted contract's `hash` share one H.  Fall back to the
       macsl builtin if no such function is in scope. *)
    let bare = String.sub fname 1 (String.length fname - 1) in
    let li =
      match Logic_env.find_all_logic_functions bare with
      | li :: _ -> li
      | [] -> List.hd (Logic_env.find_all_logic_functions fname)
    in
    let rt = match li.l_type with Some t -> t | None -> Linteger in
    Logic_const.term (Tapp (li, [], terms)) rt
  | PLapp (app_name, _, [ { lexpr_node = PLvar arg } ])
    when List.mem app_name kw_terms ->
    (match List.assoc_opt app_name termassoc with
     | Some (RepApp l) ->
       (match List.assoc_opt arg l with
        | Some t -> t
        | None -> meta_ctxt.error expr.lexpr_loc
                    "%s is not a valid argument for %s here" arg app_name)
     | Some (RepVariable _) ->
       meta_ctxt.error expr.lexpr_loc "%s expects no argument here" app_name
     | None -> meta_ctxt.error expr.lexpr_loc
                 "%s is forbidden in this context" app_name)
  | PLvar vname when List.mem vname kw_terms ->
    (match List.assoc_opt vname termassoc with
     | Some (RepVariable t) -> t
     | Some (RepApp _) ->
       meta_ctxt.error expr.lexpr_loc "%s expects an argument here" vname
     | None -> meta_ctxt.error expr.lexpr_loc
                 "%s is forbidden in this context" vname)
  | _ -> orig_ctxt.type_term meta_ctxt env expr

let type_with_assoc typing_context loc kf termassoc expr =
  ignore loc; ignore kf;
  let meta_tc =
    { typing_context with
      type_predicate = meta_type_predicate typing_context;
      type_term = meta_type_term termassoc typing_context }
  in
  let env = Logic_typing.append_here_label meta_tc.pre_state in
  let env = Logic_typing.append_pre_label env in
  let env = Logic_typing.append_old_and_post_labels env in
  meta_tc.type_predicate meta_tc env expr

(* The property is stored untyped and re-typed per site, with the
   meta-variables resolved against globals (delayed typing). *)
let delay_prop tc lexpr =
  fun kf aslist ->
    let dfind_var ?label:_ var =
      try tc.find_var var
      with Not_found ->
      try Cil.cvar_to_lvar (Globals.Vars.find_from_astinfo var Global)
      with Not_found ->
        let kf = Globals.Functions.find_by_name var in
        Cil.cvar_to_lvar (Kernel_function.get_vi kf)
    in
    let dtc = { tc with find_var = dfind_var } in
    type_with_assoc dtc lexpr.lexpr_loc kf aslist lexpr

(* ------------------------------------------------------------------ *)
(* Parsing the policy command list                                     *)
(* ------------------------------------------------------------------ *)

let as_string tc msg e = match e.lexpr_node with
  | PLconstant (StringConstant n) -> n
  | PLvar n -> n
  | _ -> tc.error e.lexpr_loc "%s" msg

let target_name tc e = match e.lexpr_node with
  | PLvar f -> f
  | _ -> tc.error e.lexpr_loc "a target must be a function name"

let rec parse_targets tc e = match e.lexpr_node with
  | PLvar "\\ALL" -> TgAll
  | PLempty -> TgSet []
  | PLset elems -> TgSet (List.map (target_name tc) elems)
  | PLapp ("\\diff", _, [ a; b ]) -> TgDiff (parse_targets tc a, parse_targets tc b)
  | _ -> tc.error e.lexpr_loc
           "\\targets supports \\ALL, {f,...}, and \\diff(T1, T2)"

let process_property tc loc = function
  | { lexpr_node = PLapp ("\\name", _, [ ename ]) }
    :: { lexpr_node = PLapp ("\\targets", _, [ etargets ]) }
    :: { lexpr_node = PLapp ("\\context", _, [ econtext ]) }
    :: tail ->
    let p_name = as_string tc "policy name must be a string" ename in
    let p_target = parse_targets tc etargets in
    let p_context = match econtext.lexpr_node with
      | PLvar "\\writing"  -> Writing
      | PLvar "\\reading"  -> Reading
      | PLvar "\\postcond" -> Postcond
      | PLvar "\\precond"  -> Precond
      | PLvar "\\noninterference" -> Noninterference
      | PLvar "\\total" -> Total
      | PLvar "\\guarded_by" -> Guarded_by
      | PLvar "\\stable_check" -> Stable_check
      | PLvar "\\authorized" -> Authorized
      | PLvar "\\tamper_evident" -> Tamper_evident
      | _ -> tc.error econtext.lexpr_loc
               "macsl supports \\context(\\writing | \\reading | \\postcond | \
                \\precond | \\noninterference | \\total | \\guarded_by | \
                \\stable_check | \\authorized | \\tamper_evident)"
    in
    let p_property, p_secret = match p_context with
      | Noninterference ->
        (* the tail names the secret parameter(s): \secret(p, ...) *)
        let secret = match tail with
          | [ { lexpr_node = PLapp ("\\secret", _, args) } ] ->
            List.map (target_name tc) args
          | _ -> tc.error loc
                   "noninterference policy expects \\secret(param, ...)"
        in
        ((fun _ _ -> Logic_const.ptrue), secret)
      | _ ->
        let eproperty = match tail with
          | [ x ] -> x
          | [] -> tc.error loc "missing the actual property predicate"
          | _ -> tc.error loc "too many trailing arguments in policy"
        in
        (delay_prop tc eproperty, [])
    in
    gathered := { p_name; p_target; p_context; p_property; p_secret; p_loc = loc }
                :: !gathered;
    Ext_terms [ Logic_const.tstring ~loc p_name ]
  | _ -> tc.error loc
           "invalid policy: expected \\prop, \\name(..), \\targets(..), \
            \\context(..), P"

let process_meta tc loc l = match l with
  | command :: t ->
    (match command.lexpr_node with
     | PLvar "\\prop" -> process_property tc loc t
     (* an already-processed policy reprints as its name string *)
     | PLconstant (StringConstant s) -> Ext_terms [ Logic_const.tstring ~loc s ]
     | _ -> tc.error loc "invalid command (expected \\prop)")
  | [] -> tc.error loc "missing command"

let register_parsing () =
  register_builtins ();
  (* macsl owns the `happy` keyword; it deliberately does NOT squat `meta`
     (MetAcsl's), so the two plugins can be loaded together. *)
  Acsl_extension.register_global ~plugin:"macsl" "happy" process_meta true

(* ------------------------------------------------------------------ *)
(* Instrumentation: emit an assert at each write site (in place)       *)
(* ------------------------------------------------------------------ *)

let emitter =
  Emitter.create "macsl" ~correctness:[] ~tuning:[] [ Emitter.Code_annot ]

let addr_of_tlval tlval =
  Logic_utils.mk_logic_AddrOf tlval (Cil.typeOfTermLval tlval)
let addr_of_tlhost (h, _) = addr_of_tlval (h, TNoOffset)

let counter = ref 0

(* Build and add one assert for [pol] at [stmt], with the meta-variables bound
   by [assoc].  Returns true iff a (non-trivial) assertion was emitted. *)
let instantiate pol kf stmt assoc =
  let pred = pol.p_property kf assoc in
  if Logic_utils.is_trivially_true pred then false
  else begin
    let label =
      if Number_assertions.get ()
      then (incr counter; Printf.sprintf "%s_%d" pol.p_name !counter)
      else pol.p_name
    in
    let named = { pred with pred_name = label :: "meta" :: pred.pred_name } in
    let annot =
      Logic_const.(new_code_annotation
                     (AAssert ([], toplevel_predicate ~kind:Assert named)))
    in
    Annotations.add_code_annot emitter ~kf stmt annot;
    true
  end

(* H-R: inject [pol]'s predicate as a *checked* postcondition on [kf] (no
   meta-variable substitution — the predicate is whole, over globals + \old).
   `Check` means WP must prove it but callers do not get to assume it. *)
let emit_ensures pol kf =
  let pred = pol.p_property kf [] in
  if Logic_utils.is_trivially_true pred then false
  else begin
    let label =
      if Number_assertions.get ()
      then (incr counter; Printf.sprintf "%s_%d" pol.p_name !counter)
      else pol.p_name
    in
    let named = { pred with pred_name = label :: "meta" :: pred.pred_name } in
    let ip = Logic_const.new_predicate ~kind:Check named in
    Annotations.add_ensures emitter kf [ (Normal, ip) ];
    true
  end

(* H-S: inject [pol]'s predicate as a normal precondition (capability) on the
   guarded function [kf].  A normal `requires` is *assumed* by the body but
   *checked by WP at every call site* — that call-site obligation is what
   catches an unauthenticated caller, in the caller that took the shortcut. *)
let emit_requires pol kf =
  let pred = pol.p_property kf [] in
  if Logic_utils.is_trivially_true pred then false
  else begin
    let label =
      if Number_assertions.get ()
      then (incr counter; Printf.sprintf "%s_%d" pol.p_name !counter)
      else pol.p_name
    in
    let named = { pred with pred_name = label :: "meta" :: pred.pred_name } in
    let ip = Logic_const.new_predicate named in
    Annotations.add_requires emitter kf [ ip ];
    true
  end

(* H-D: add a `terminates` clause (the totality claim) to the target function.
   WP must then prove it — discharged from the function's `loop variant`s, so a
   missing or non-decreasing variant turns the termination goal red.  This is the
   "always returns" half; the "never faults" half is `-wp-rte` at run time.  We
   deliberately do NOT skip a trivially-\true predicate: the whole point is to
   attach the clause so WP checks termination.  (The roadmap's `\fuel(expr)`
   bounded-work ghost and a hard meta-pass error on a variant-less loop are
   refinements left as TODO — WP already reddens a variant-less/looping target.) *)
let emit_terminates pol kf =
  let pred = pol.p_property kf [] in
  let label =
    if Number_assertions.get ()
    then (incr counter; Printf.sprintf "%s_%d" pol.p_name !counter)
    else pol.p_name
  in
  let named = { pred with pred_name = label :: "meta" :: pred.pred_name } in
  let ip = Logic_const.new_predicate named in
  Annotations.add_terminates emitter kf ip;
  true

(* H-I2: noninterference via SELF-COMPOSITION.  Synthesize a twin driver
   `f__selfcomp` that calls the target [kf] twice — public parameters shared,
   secret parameters distinct (p_a / p_b) — and asserts the two results are
   equal.  WP discharges it modularly from [kf]'s functional contract: if the
   result depends on a secret, the relational assert is unprovable (a leak).
   This is the one genuinely relational (2-safety) property; see clone.ml for
   the add-a-synthesized-function pattern. *)
let emit_selfcomp pol kf =
  let fname = Kernel_function.get_name kf in
  let formals = Kernel_function.get_formals kf in
  let rettype = Kernel_function.get_return_type kf in
  if formals = [] || Ast_types.is_void rettype then begin
    Self.warning
      "noninterference: %s needs >=1 parameter and a non-void result; skipped"
      fname;
    false
  end else begin
    let loc = Cil_datatype.Location.unknown in
    let is_secret vi = List.mem vi.vname pol.p_secret in
    List.iter
      (fun s ->
         if not (List.exists (fun vi -> vi.vname = s) formals) then
           Self.warning "noninterference: %s has no parameter named %s" fname s)
      pol.p_secret;
    let driver = Cil.emptyFunction (fname ^ "__selfcomp") in
    Cil.setReturnType driver Cil_const.voidType;
    (* public params shared; secret params split into _a / _b copies *)
    let slots =
      List.map
        (fun vi ->
           if is_secret vi then
             let a = Cil.makeFormalVar driver (vi.vname ^ "_a") vi.vtype in
             let b = Cil.makeFormalVar driver (vi.vname ^ "_b") vi.vtype in
             `Sec (a, b)
           else `Pub (Cil.makeFormalVar driver vi.vname vi.vtype))
        formals
    in
    let args first =
      List.map
        (function
          | `Pub p -> Cil.evar p
          | `Sec (a, b) -> Cil.evar (if first then a else b))
        slots
    in
    let ra = Cil.makeLocalVar driver "ra" rettype in
    let rb = Cil.makeLocalVar driver "rb" rettype in
    (* in 32.1 the callee of a Call is an lhost (not an exp) *)
    let callee = Var (Kernel_function.get_vi kf) in
    let call first r =
      Cil.mkStmtOneInstr (Call (Some (Var r, NoOffset), callee, args first, loc))
    in
    let ret = Cil.mkStmt (Return (None, loc)) in
    driver.sbody <- Cil.mkBlock [ call true ra; call false rb; ret ];
    Cfg.clearCFGinfo ~clear_id:false driver;
    Cfg.cfgFun driver;
    Globals.Functions.replace_by_definition (Cil.empty_funspec ()) driver loc;
    let dkf = Globals.Functions.get driver.svar in
    let f = Ast.get () in
    f.globals <- f.globals @ [ GFun (driver, loc) ];
    Ast.mark_as_grown ();
    (* the relational obligation: equal public inputs => equal public output *)
    let tra = Logic_const.tvar (Cil.cvar_to_lvar ra) in
    let trb = Logic_const.tvar (Cil.cvar_to_lvar rb) in
    let pred = Logic_const.prel (Req, tra, trb) in
    let named = { pred with pred_name = [ pol.p_name; "meta" ] } in
    let annot =
      Logic_const.(new_code_annotation
                     (AAssert ([], toplevel_predicate ~kind:Assert named)))
    in
    Annotations.add_code_annot emitter ~kf:dkf ret annot;
    true
  end

let writing_assoc tlval =
  [ "\\written",       RepVariable (addr_of_tlval tlval);
    "\\lhost_written", RepVariable (addr_of_tlhost tlval) ]

let reading_assoc tlval =
  [ "\\read",       RepVariable (addr_of_tlval tlval);
    "\\lhost_read", RepVariable (addr_of_tlhost tlval) ]

(* ---- H-T: writing context (Phase 0) -------------------------------- *)
class writing_visitor pol = object (self)
  inherit Visitor.frama_c_inplace
  val mutable count = 0
  method get_count = count

  method private emit stmt tlval =
    let kf = Option.get self#current_kf in
    if instantiate pol kf stmt (writing_assoc tlval) then count <- count + 1

  method! vstmt_aux stmt =
    if not stmt.ghost then
      (match stmt.skind with
       | Instr (Set (lval, _, _)) ->
         self#emit stmt (Logic_utils.lval_to_term_lval lval)
       | Instr (Call (Some lval, _, _, _)) ->
         self#emit stmt (Logic_utils.lval_to_term_lval lval)
       | Instr (Local_init (vi, _, _)) ->
         self#emit stmt (Logic_utils.lval_to_term_lval (Cil.var vi))
       | _ -> ());
    Cil.DoChildren
end

(* ---- H-I1: reading context (Phase 1) ------------------------------- *)
(* The mirror of the writing pass: collect the lvalues *read* at each statement
   (i.e. lvals occurring inside expressions, not the write-target lval), then
   emit one separation assert per read.  Technique (after MetAcsl): an [in_exp]
   flag so vlval only counts reads; AddrOf/SizeOf handled; deduped per stmt. *)
module TLvalSet = Cil_datatype.Term_lval.Set
module StmtHashtbl = Cil_datatype.Stmt.Hashtbl

class reading_visitor pol = object (self)
  inherit Visitor.frama_c_inplace
  val mutable count = 0
  method get_count = count

  val lvals_by_stmt = StmtHashtbl.create 20
  val mutable in_exp = false

  method private emit stmt tlval =
    let kf = Option.get self#current_kf in
    if instantiate pol kf stmt (reading_assoc tlval) then count <- count + 1

  method! vexpr e =
    in_exp <- true;
    (match e.enode with
     | SizeOfE _ | AlignOfE _ ->
       (* the value is not evaluated, only its type *)
       in_exp <- false; Cil.SkipChildren
     | AddrOf (_, o) | StartOf (_, o) ->
       (* the toplevel lval is not read; its offset indices are *)
       ignore (Visitor.visitFramacOffset (self :> Visitor.frama_c_visitor) o);
       in_exp <- false; Cil.SkipChildren
     | _ -> Cil.DoChildrenPost (fun e -> in_exp <- false; e))

  method! vlval lval =
    let typ = Cil.typeOfLval lval in
    if in_exp && not (Ast_types.is_fun typ) then
      (match self#current_stmt with
       | Some stmt ->
         (match stmt.skind with
          | UnspecifiedSequence _ -> ()    (* ignore the US bookkeeping lvals *)
          | _ ->
            let tl = Logic_utils.lval_to_term_lval lval in
            let old =
              match StmtHashtbl.find_opt lvals_by_stmt stmt with
              | Some s -> s | None -> TLvalSet.empty
            in
            StmtHashtbl.replace lvals_by_stmt stmt (TLvalSet.add tl old))
       | None -> ());
    Cil.DoChildren

  method! vstmt_aux stmt =
    if not stmt.ghost then
      let after s =
        (match StmtHashtbl.find_opt lvals_by_stmt s with
         | Some set -> TLvalSet.iter (self#emit s) set
         | None -> ());
        s
      in
      Cil.DoChildrenPost after
    else Cil.DoChildren
end

let rec kfs_of_target = function
  | TgAll ->
    List.rev
      (Globals.Functions.fold
         (fun kf acc ->
            if Kernel_function.has_definition kf then kf :: acc else acc) [])
  | TgSet names ->
    List.filter_map
      (fun n ->
         try Some (Globals.Functions.find_by_name n)
         with Not_found ->
           Self.warning "unknown target function %s; skipped" n; None)
      names
  | TgDiff (a, b) ->
    let excluded = kfs_of_target b in
    List.filter
      (fun kf -> not (List.exists (Kernel_function.equal kf) excluded))
      (kfs_of_target a)

let visit_all (vis : Visitor.frama_c_visitor) kfs =
  List.iter
    (fun kf ->
       ignore (Visitor.visitFramacFunction vis (Kernel_function.get_definition kf)))
    kfs

let run_policy pol =
  let kfs = kfs_of_target pol.p_target in
  (* the body-walking contexts need a definition; the contract/synthesis
     contexts accept declaration-only targets (they use the contract). *)
  let kfs = match pol.p_context with
    | Writing | Reading | Total | Guarded_by | Stable_check | Authorized ->
      List.filter
        (fun kf ->
           if Kernel_function.has_definition kf then true
           else (Self.warning "target %a has no definition; skipped"
                   Kernel_function.pretty kf; false))
        kfs
    | Postcond | Precond | Noninterference | Tamper_evident -> kfs
  in
  let n =
    match pol.p_context with
    | Writing ->
      let v = new writing_visitor pol in
      visit_all (v :> Visitor.frama_c_visitor) kfs; v#get_count
    | Reading ->
      let v = new reading_visitor pol in
      visit_all (v :> Visitor.frama_c_visitor) kfs; v#get_count
    (* WS1 stage 1: both concurrency contexts inject their (uninterpreted)
       obligation at every write site of the target, reusing the H-T walk.
       \guarded_by carries `\held(L)`; \stable_check carries `\stable(G)`. *)
    | Guarded_by | Stable_check ->
      let v = new writing_visitor pol in
      visit_all (v :> Visitor.frama_c_visitor) kfs; v#get_count
    (* WS3 (M-3): the principal-identity obligation is injected at every write
       site of the protected operation, reusing the H-T walk — exactly like
       \guarded_by, but the predicate is `authorized(current_principal, OP)`. *)
    | Authorized ->
      let v = new writing_visitor pol in
      visit_all (v :> Visitor.frama_c_visitor) kfs; v#get_count
    (* WS4 (M-4): the hash-chain obligation is a checked postcondition (the
       chaining discipline), reusing the H-R emit_ensures path. *)
    | Tamper_evident ->
      List.fold_left (fun acc kf -> if emit_ensures pol kf then acc + 1 else acc)
        0 kfs
    | Postcond ->
      List.fold_left (fun acc kf -> if emit_ensures pol kf then acc + 1 else acc)
        0 kfs
    | Precond ->
      List.fold_left (fun acc kf -> if emit_requires pol kf then acc + 1 else acc)
        0 kfs
    | Noninterference ->
      List.fold_left (fun acc kf -> if emit_selfcomp pol kf then acc + 1 else acc)
        0 kfs
    | Total ->
      List.fold_left (fun acc kf -> if emit_terminates pol kf then acc + 1 else acc)
        0 kfs
  in
  let descr, ctx = match pol.p_context with
    | Writing  -> "write site",      "writing"
    | Reading  -> "read site",       "reading"
    | Postcond -> "target function", "postcond"
    | Precond  -> "target function", "precond"
    | Noninterference -> "target function", "noninterference"
    | Total    -> "target function", "total"
    | Guarded_by -> "guarded write site", "guarded_by"
    | Stable_check -> "check-then-act site", "stable_check"
    | Authorized -> "protected operation site", "authorized"
    | Tamper_evident -> "target function", "tamper_evident" in
  if n = 0 then
    Self.warning ~wkey:zero_wkey
      "policy %s expanded to 0 obligations (matched no %s)" pol.p_name descr;
  if List_targets.get () then
    Self.result "policy %s [%s]: %d assertion(s) over %d target function(s)"
      pol.p_name ctx n (List.length kfs);
  n

let run (_file : Cil_types.file) =
  if Enabled.get () then begin
    let sel = Targets.get () in
    let pols = List.rev !gathered in
    let pols =
      if Datatype.String.Set.is_empty sel then pols
      else List.filter (fun p -> Datatype.String.Set.mem p.p_name sel) pols
    in
    Self.feedback "Will process %d policies" (List.length pols);
    let total = List.fold_left (fun acc p -> acc + run_policy p) 0 pols in
    Self.feedback
      "Instrumented %d assertion(s) in place — run -wp next (no -then-last)."
      total
  end

(* Instrument right after the AST is computed (NOT as a -main analysis), so any
   later analysis in the same run — `-macsl -wp`, `-macsl -eva` — sees the
   generated asserts.  This is what removes MetAcsl's -then-last footgun. *)
let () =
  Ast.apply_after_computed run;
  register_parsing ()
