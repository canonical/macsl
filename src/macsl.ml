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

type context = Writing | Reading

type target = TgAll | TgSet of string list

(* What a meta-variable (\written, ...) is replaced by at a site *)
type replaced_kind =
  | RepVariable of term
  | RepApp of (string * term) list

type policy = {
  p_name    : string;
  p_target  : target;
  p_context : context;
  (* the property, re-typed per site once the meta-variables are bound *)
  p_property : Kernel_function.t -> (string * replaced_kind) list -> predicate;
  p_loc     : location;
}

(* Policies gathered while the ACSL extension is parsed. *)
let gathered : policy list ref = ref []

(* ------------------------------------------------------------------ *)
(* Builtin keywords so the predicate type-checks                       *)
(* ------------------------------------------------------------------ *)

(* commands/contexts are predicate builtins; meta-variables are term builtins *)
let kw_preds = [ "\\prop"; "\\writing"; "\\reading"; "\\calling";
                 "\\weak_invariant"; "\\strong_invariant" ]
let kw_terms = [ "\\written"; "\\lhost_written"; "\\read"; "\\called" ]

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
    kw_terms

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

let parse_targets tc e = match e.lexpr_node with
  | PLvar "\\ALL" -> TgAll
  | PLempty -> TgSet []
  | PLset elems -> TgSet (List.map (target_name tc) elems)
  | _ -> tc.error e.lexpr_loc
           "Phase 0 supports \\targets(\\ALL) or \\targets({f,...})"

let process_property tc loc = function
  | { lexpr_node = PLapp ("\\name", _, [ ename ]) }
    :: { lexpr_node = PLapp ("\\targets", _, [ etargets ]) }
    :: { lexpr_node = PLapp ("\\context", _, [ econtext ]) }
    :: tail ->
    let p_name = as_string tc "policy name must be a string" ename in
    let p_target = parse_targets tc etargets in
    let p_context = match econtext.lexpr_node with
      | PLvar "\\writing" -> Writing
      | PLvar "\\reading" -> Reading
      | _ -> tc.error econtext.lexpr_loc
               "macsl supports \\context(\\writing) and \\context(\\reading)"
    in
    let eproperty = match tail with
      | [ x ] -> x
      | [] -> tc.error loc "missing the actual property predicate"
      | _ -> tc.error loc "too many trailing arguments in policy"
    in
    let p_property = delay_prop tc eproperty in
    gathered := { p_name; p_target; p_context; p_property; p_loc = loc }
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

let kfs_of_target = function
  | TgAll ->
    List.rev
      (Globals.Functions.fold
         (fun kf acc ->
            if Kernel_function.has_definition kf then kf :: acc else acc) [])
  | TgSet names ->
    List.filter_map
      (fun n ->
         try
           let kf = Globals.Functions.find_by_name n in
           if Kernel_function.has_definition kf then Some kf
           else (Self.warning "target %s has no definition; skipped" n; None)
         with Not_found ->
           Self.warning "unknown target function %s; skipped" n; None)
      names

let visit_all (vis : Visitor.frama_c_visitor) kfs =
  List.iter
    (fun kf ->
       ignore (Visitor.visitFramacFunction vis (Kernel_function.get_definition kf)))
    kfs

let run_policy pol =
  let kfs = kfs_of_target pol.p_target in
  let n =
    match pol.p_context with
    | Writing ->
      let v = new writing_visitor pol in
      visit_all (v :> Visitor.frama_c_visitor) kfs; v#get_count
    | Reading ->
      let v = new reading_visitor pol in
      visit_all (v :> Visitor.frama_c_visitor) kfs; v#get_count
  in
  let site, ctx = match pol.p_context with
    | Writing -> "write", "writing"
    | Reading -> "read",  "reading" in
  if n = 0 then
    Self.warning ~wkey:zero_wkey
      "policy %s expanded to 0 assertions (matched no %s site)" pol.p_name site;
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
