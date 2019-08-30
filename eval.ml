(****************************************************************
 * ASL evaluator
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** ASL evaluator *)

module PP   = Asl_parser_pp
module AST  = Asl_ast
module TC   = Tcheck

open AST
open Printf
open Utils
open Asl_utils
open Value

(****************************************************************
 * Flags to control behaviour (mostly for debugging)
 ****************************************************************)

(** Debugging output on every variable write *)
let trace_write = ref false

(** Debugging output on every function call *)
let trace_funcall = ref false

(** Debugging output on every primitive function or function call *)
let trace_primop = ref false

(** Debugging output on every instruction execution *)
let trace_instruction = ref false


(** It is an error to have multiple function definitions with conflicting types.
 *  But, for historical reasons, we still allow multiple definitions and later
 *  definitions override earlier definitions.
 *)
let override_conflicts = true


(****************************************************************)
(** {2 Lookup table for IMPLEMENTATION_DEFINED values}          *)
(****************************************************************)

module ImpDefs = struct
    include Map.Make(struct
        type t = string
        let compare = String.compare
    end)
end


(****************************************************************)
(** {2 Scopes}                                                  *)
(****************************************************************)

(** Basically just a mutable binding *)
type scope = { mutable bs : value Bindings.t; }

let empty_scope (_: unit): scope =
    let bs = Bindings.empty in
    { bs }

let mem_scope (k: ident) (s: scope): bool =
    Bindings.mem k s.bs

let get_scope (k: ident) (s: scope): value =
    Bindings.find k s.bs

let get_scope_opt (k: ident) (s: scope): value option =
    Bindings.find_opt k s.bs

let set_scope (k: ident) (v: value) (s: scope): unit =
    s.bs <- Bindings.add k v s.bs


(****************************************************************)
(** {2 Mutable bindings}                                        *)
(****************************************************************)

(** Environment representing both global and local state of the system *)
module Env : sig
    type t
    val empty               : t
    val nestTop             : (t -> 'a) -> (t -> 'a)
    val nest                : (t -> 'a) -> (t -> 'a)

    val addLocalVar         : AST.l -> t -> ident -> value -> unit
    val addLocalConst       : AST.l -> t -> ident -> value -> unit

    val addGlobalConst      : t -> ident -> value -> unit
    val getGlobalConst      : t -> ident -> value

    (* to support generation of unknown values, we need to remember the structure
     * of user-defined types such as enumerations and records
     *)
    val addEnum             : t -> ident -> value list -> unit
    val getEnum             : t -> ident -> (value list) option
    val isEnumEq            : t -> ident -> bool
    val isEnumNeq           : t -> ident -> bool

    val addRecord           : t -> ident -> (AST.ty * ident) list -> unit
    val getRecord           : t -> ident -> (AST.ty * ident) list option

    val addTypedef          : t -> ident -> AST.ty -> unit
    val getTypedef          : t -> ident -> AST.ty option

    val addGlobalVar        : t -> ident -> value -> unit
    val getVar              : AST.l -> t -> ident -> value
    val setVar              : AST.l -> t -> ident -> value -> unit

    val getFun              : AST.l -> t -> ident -> (ident list * ident list * AST.l * stmt list)
    val addFun              : AST.l -> t -> ident -> (ident list * ident list * AST.l * stmt list) -> unit

    val getInstruction      : AST.l -> t -> ident -> (encoding * (stmt list) option * bool * stmt list)
    val addInstruction      : AST.l -> t -> ident -> (encoding * (stmt list) option * bool * stmt list) -> unit

    val getDecoder          : t -> ident -> decode_case
    val addDecoder          : t -> ident -> decode_case -> unit

    val setImpdef           : t -> string -> value -> unit
    val getImpdef           : AST.l -> t -> string -> value

end = struct
    type t = {
        mutable instructions : (encoding * (stmt list) option * bool * stmt list) Bindings.t;
        mutable decoders     : decode_case Bindings.t;
        mutable functions    : (ident list * ident list * AST.l * stmt list) Bindings.t;
        mutable enums        : (value list) Bindings.t;
        mutable enumEqs      : IdentSet.t;
        mutable enumNeqs     : IdentSet.t;
        mutable records      : ((AST.ty * ident) list) Bindings.t;
        mutable typedefs     : AST.ty Bindings.t;
        mutable globals      : scope;
        mutable constants    : scope;
        mutable impdefs      : value ImpDefs.t;
        mutable locals       : scope list
    }

    let empty = {
        decoders     = Bindings.empty;
        instructions = Bindings.empty;
        functions    = Bindings.empty;
        enums        = Bindings.empty;
        enumEqs      = IdentSet.empty;
        enumNeqs     = IdentSet.empty;
        records      = Bindings.empty;
        typedefs     = Bindings.empty;
        globals      = empty_scope ();
        constants    = empty_scope ();
        impdefs      = ImpDefs.empty;
        locals       = [empty_scope ()];
    }

    let nestTop (k: t -> 'a) (parent: t): 'a =
        let child = {
            decoders     = parent.decoders;
            instructions = parent.instructions;
            functions    = parent.functions;
            enums        = parent.enums;
            enumEqs      = parent.enumEqs;
            enumNeqs     = parent.enumNeqs;
            records      = parent.records;
            typedefs     = parent.typedefs;
            globals      = parent.globals;
            constants    = parent.constants;
            impdefs      = parent.impdefs;
            locals       = [empty_scope ()];  (* only change *)
        } in
        k child

    let nest (k: t -> 'a) (parent: t): 'a =
        let child = {
            decoders     = parent.decoders;
            instructions = parent.instructions;
            functions    = parent.functions;
            enums        = parent.enums;
            enumEqs      = parent.enumEqs;
            enumNeqs     = parent.enumNeqs;
            records      = parent.records;
            typedefs     = parent.typedefs;
            globals      = parent.globals;
            constants    = parent.constants;
            impdefs      = parent.impdefs;
            locals       = empty_scope () :: parent.locals;  (* only change *)
        } in
        k child

    let addLocalVar (loc: l) (env: t) (x: ident) (v: value): unit =
        if !trace_write then Printf.printf "TRACE: fresh %s = %s\n" (pprint_ident x) (pp_value v);
        (match env.locals with
        | (bs :: _) -> set_scope x v bs
        | []        -> raise (EvalError (loc, "addLocalVar"))
        )

    let addLocalConst (loc: l) (env: t) (x: ident) (v: value): unit =
        (* todo: should constants be held separately from local vars? *)
        (match env.locals with
        | (bs :: _) -> set_scope x v bs
        | []        -> raise (EvalError (loc, "addLocalConst"))
        )

    let addGlobalConst (env: t) (x: ident) (v: value): unit =
        set_scope x v env.constants

    let getGlobalConst (env: t) (x: ident): value =
        get_scope x env.constants

    let addEnum (env: t) (x: ident) (vs: value list): unit =
        env.enums    <- Bindings.add x vs env.enums

    let getEnum (env: t) (x: ident): (value list) option =
        Bindings.find_opt x env.enums

    let isEnumEq  (env: t) (x: ident): bool = IdentSet.mem x env.enumEqs
    let isEnumNeq (env: t) (x: ident): bool = IdentSet.mem x env.enumNeqs

    let addRecord (env: t) (x: ident) (fs: (AST.ty * ident) list): unit =
        env.records <- Bindings.add x fs env.records

    let getRecord (env: t) (x: ident): ((AST.ty * ident) list) option =
        Bindings.find_opt x env.records

    let addTypedef (env: t) (x: ident) (ty: AST.ty): unit =
        env.typedefs <- Bindings.add x ty env.typedefs

    let getTypedef (env: t) (x: ident): AST.ty option =
        Bindings.find_opt x env.typedefs

    let addGlobalVar (env: t) (x: ident) (v: value): unit =
        set_scope x v env.globals

    let findScope (env: t) (x: ident): scope option =
        let rec search (bss : scope list): scope option =
            (match bss with
            | (bs :: bss') ->
                    if mem_scope x bs then Some bs else search bss'
            | [] ->
                    if mem_scope x env.globals then Some env.globals
                    else if mem_scope x env.constants then Some env.constants
                    else None
            )
        in
        search env.locals

    let getVar (loc: l) (env: t) (x: ident): value =
        (match findScope env x with
        | Some bs -> get_scope x bs
        | None    -> raise (EvalError (loc, "getVar: " ^ pprint_ident x))
        )

    let setVar (loc: l) (env: t) (x: ident) (v: value): unit =
        if !trace_write then Printf.printf "TRACE: write %s = %s\n" (pprint_ident x) (pp_value v);
        (match findScope env x with
        | Some bs -> set_scope x v bs
        | None    -> raise (EvalError (loc, "setVar " ^ pprint_ident x))
        )

    let getFun (loc: l) (env: t) (x: ident): (ident list * ident list * AST.l * stmt list) =
        (match Bindings.find_opt x env.functions with
        | Some def -> def
        | None     -> raise (EvalError (loc, "getFun " ^ pprint_ident x))
        )

    let addFun (loc: l) (env: t) (x: ident) (def: (ident list * ident list * AST.l * stmt list)): unit =
        if false then Printf.printf "Adding function %s\n" (pprint_ident x);
        if Bindings.mem x env.functions then begin
            if true then begin
                () (* silently override *)
            end else if override_conflicts then begin
                (* backward compatibility mode: only report a stern warning *)
                Printf.printf "Stern warning: %s function %s conflicts with earlier definition - discarding earlier definition\n"
                    (pp_loc loc) (pprint_ident x);
            end else begin
                raise (TC.Ambiguous (loc, "function definition", pprint_ident x))
            end
        end;
        env.functions <- Bindings.add x def env.functions

    let getInstruction (loc: AST.l) (env: t) (x: ident): (encoding * (stmt list) option * bool * stmt list) =
        Bindings.find x env.instructions

    let addInstruction (loc: AST.l) (env: t) (x: ident) (instr: encoding * (stmt list) option * bool * stmt list): unit =
        env.instructions <- Bindings.add x instr env.instructions

    let getDecoder (env: t) (x: ident): decode_case =
        Bindings.find x env.decoders

    let addDecoder (env: t) (x: ident) (d: decode_case): unit =
        env.decoders <- Bindings.add x d env.decoders

    let setImpdef (env: t) (x: string) (v: value): unit =
        env.impdefs <- ImpDefs.add x v env.impdefs

    let getImpdef (loc: l) (env: t) (x: string): value =
        (match ImpDefs.find_opt x env.impdefs with
        | Some v -> v
        | None ->
                raise (EvalError (loc, "Unknown value for IMPLEMENTATION_DEFINED \""^x^"\""))
        )
end


(****************************************************************)
(** {2 Evaluation functions}                                    *)
(****************************************************************)

(** Evaluate list of expressions *)
let rec eval_exprs (loc: l) (env: Env.t) (xs: AST.expr list): value list =
    List.map (eval_expr loc env) xs

(** Create uninitialized value at given type

    - For any scalar type, this is the value VUninitialized.
    - For any composite type, all elements are set to uninitialized values

    todo: bitvectors are currently set to UNKNOWN because the bitvector
    representation currently in use cannot track uninitialized bits
 *)
and mk_uninitialized (loc: l) (env: Env.t) (x: AST.ty): value =
    ( match x with
    | Type_Constructor(tc) ->
        (match Env.getRecord env tc with
        | Some fs ->
            mkrecord (List.map (fun (ty, f) -> (f, mk_uninitialized loc env ty)) fs)
        | None ->
            (match Env.getTypedef env tc with
            | Some ty' -> mk_uninitialized loc env ty'
            | None     -> VUninitialized
            )
        )
    | Type_Array(Index_Enum(tc),ety) ->
            Value.empty_array (mk_uninitialized loc env ety)
    | Type_Array(Index_Range(lo,hi),ety) ->
            Value.empty_array (mk_uninitialized loc env ety)
    | Type_Tuple(tys) ->
            VTuple (List.map (mk_uninitialized loc env) tys)
    (* bitvectors and registers should really track whether a bit is initialized individually *)
    | Type_Bits(n) -> eval_unknown_bits (to_integer loc (eval_expr loc env n))
    | Type_Register(wd, _) -> eval_unknown_bits (Z.of_string wd)
    | _ ->
            VUninitialized (* should only be used for scalar types *)
    )

(** Evaluate UNKNOWN at given type *)
and eval_unknown (loc: l) (env: Env.t) (x: AST.ty): value =
    ( match x with
    | Type_Constructor(Ident "integer") -> eval_unknown_integer ()
    | Type_Constructor(Ident "real")    -> eval_unknown_real ()
    | Type_Constructor(Ident "string")  -> eval_unknown_string ()
    | Type_Constructor(tc) ->
        (match Env.getEnum env tc with
        | Some (e::_) -> e
        | Some [] -> raise (EvalError (loc, "eval_unknown unknown type constructor " ^ Utils.to_string (PP.pp_ty x)))
        | None ->
            (match Env.getRecord env tc with
            | Some fs ->
                mkrecord (List.map (fun (ty, f) -> (f, eval_unknown loc env ty)) fs)
            | None ->
                (match Env.getTypedef env tc with
                | Some ty' -> eval_unknown loc env ty'
                | None ->
                    raise (EvalError (loc, "eval_unknown " ^ Utils.to_string (PP.pp_ty x)))
                )
            )
        )
    | Type_Bits(n) -> eval_unknown_bits (to_integer loc (eval_expr loc env n))
    | Type_App(Ident "__RAM", [a]) ->
            let a' = to_integer loc (eval_expr loc env a) in
            eval_unknown_ram a'
    | Type_App(tc, es) ->
            raise (EvalError (loc, "eval_unknown App " ^ Utils.to_string (PP.pp_ty x)))
    | Type_OfExpr(e) ->
            raise (EvalError (loc, "eval_unknown typeof " ^ Utils.to_string (PP.pp_ty x)))
    | Type_Register(wd, _) -> eval_unknown_bits (Z.of_string wd)
    | Type_Array(Index_Enum(tc),ety) ->
            Value.empty_array (eval_unknown loc env ety)
    | Type_Array(Index_Range(lo,hi),ety) ->
            Value.empty_array (eval_unknown loc env ety)
    | Type_Tuple(tys) ->
            VTuple (List.map (eval_unknown loc env) tys)
    )

(** Evaluate pattern match *)
and eval_pattern (loc: l) (env: Env.t) (v: value) (x: AST.pattern): bool =
    ( match x with
    | Pat_LitInt(l)  -> eval_eq_int  loc v (from_intLit l)
    | Pat_LitHex(l)  -> eval_eq_int  loc v (from_hexLit l)
    | Pat_LitBits(l) -> eval_eq_bits loc v (from_bitsLit l)
    | Pat_LitMask(l) -> eval_inmask  loc v (from_maskLit l)
    | Pat_Const(c)   -> eval_eq      loc v (Env.getGlobalConst env c)
    | Pat_Wildcard   -> true
    | Pat_Tuple(ps) ->
            let vs = of_tuple loc v in
            assert (List.length vs = List.length ps);
            List.for_all2 (eval_pattern loc env) vs ps
    | Pat_Set(ps) ->
            List.exists (eval_pattern loc env v) ps
    | Pat_Single(e) ->
            let v' = eval_expr loc env e in
            eval_eq loc v v'
    | Pat_Range(lo, hi) ->
            let lo' = eval_expr loc env lo in
            let hi' = eval_expr loc env hi in
            eval_leq loc lo' v && eval_leq loc v hi'
    )

(** Evaluate bitslice bounds *)
and eval_slice (loc: l) (env: Env.t) (x: AST.slice): (value * value) =
    (match x with
    | Slice_Single(i) ->
            let i' = eval_expr loc env i in
            (i', VInt Z.one)
    | Slice_HiLo(hi, lo) ->
            let hi' = eval_expr loc env hi in
            let lo' = eval_expr loc env lo in
            let wd' = eval_add_int loc (eval_sub_int loc hi' lo') (VInt Z.one) in
            (lo', wd')
    | Slice_LoWd(lo, wd) ->
            let lo' = eval_expr loc env lo in
            let wd' = eval_expr loc env wd in
            (lo', wd')
    )

(** Evaluate expression *)
and eval_expr (loc: l) (env: Env.t) (x: AST.expr): value =
    (match x with
    | Expr_If(c, t, els, e) ->
            let rec eval_if xs d = match xs with
                | [] -> eval_expr loc env d
                | AST.E_Elsif_Cond (cond, b)::xs' ->
                    if to_bool loc (eval_expr loc env cond) then
                        eval_expr loc env b
                    else
                        eval_if xs' d
            in
            eval_if (E_Elsif_Cond(c, t)::els) e
    | Expr_Binop(a, op, b) ->
            raise (EvalError (loc, "binary operation should have been removed in expression "
                   ^ Utils.to_string (PP.pp_expr x)))
    | Expr_Field(e, f) ->
            get_field loc (eval_expr loc env e) f
    | Expr_Fields(e, fs) ->
            let v  = eval_expr loc env e in
            let vs = List.map (get_field loc v) fs in
            eval_concat loc vs
    | Expr_Slices(e, ss) ->
            let v  = eval_expr loc env e in
            let vs = List.map (fun s ->
                let (i, w) = eval_slice loc env s in
                extract_bits'' loc v i w
            ) ss in
            eval_concat loc vs
    | Expr_In(e, p) ->
            from_bool (eval_pattern loc env (eval_expr loc env e) p)
    | Expr_Var(v) ->
            Env.getVar loc env v
    | Expr_Parens(e) ->
            let v = eval_expr loc env e in
            v
    | Expr_TApply(f, tes, es) ->
            (* First deal with &&, || and IMPLIES all of which only evaluate
             * their second argument if they need to
             *)
            if name_of_FIdent f = "and_bool" then begin
                (match (tes, es) with
                | ([], [x; y]) ->
                    if to_bool loc (eval_expr loc env x) then
                        eval_expr loc env y
                    else
                        from_bool false
                | _ ->
                    raise (EvalError (loc, "malformed and_bool expression "
                       ^ Utils.to_string (PP.pp_expr x)))
                )
            end else if name_of_FIdent f = "or_bool" then begin
                (match (tes, es) with
                | ([], [x; y]) ->
                    if to_bool loc (eval_expr loc env x) then
                        from_bool true
                    else
                        eval_expr loc env y
                | _ ->
                    raise (EvalError (loc, "malformed or_bool expression "
                       ^ Utils.to_string (PP.pp_expr x)))
                )
            end else if name_of_FIdent f = "implies_bool" then begin
                (match (tes, es) with
                | ([], [x; y]) ->
                    if to_bool loc (eval_expr loc env x) then
                        eval_expr loc env y
                    else
                        from_bool true
                | _ ->
                    raise (EvalError (loc, "malformed implies_bool expression "
                       ^ Utils.to_string (PP.pp_expr x)))
                )
            end else begin
                let tvs = eval_exprs loc env tes in
                let vs  = eval_exprs loc env es in
                eval_funcall loc env f tvs vs
            end
    | Expr_Tuple(es) ->
            let vs = List.map (eval_expr loc env) es in
            VTuple vs
    | Expr_Unop(op, e) ->
            raise (EvalError (loc, "unary operation should have been removed"))
    | Expr_Unknown(t) ->
            eval_unknown loc env t
    | Expr_ImpDef(t, Some(s)) ->
            Env.getImpdef loc env s
    | Expr_ImpDef(t, None) ->
            raise (EvalError (loc, "unnamed IMPLEMENTATION_DEFINED behavior"))
    | Expr_Array(a, i) ->
            let a' = eval_expr loc env a in
            let i' = eval_expr loc env i in
            get_array loc a' i'
    | Expr_LitInt(i) -> from_intLit i
    | Expr_LitHex(i) -> from_hexLit i
    | Expr_LitReal(r) -> from_realLit r
    | Expr_LitBits(b) -> from_bitsLit b
    | Expr_LitMask(b) -> from_maskLit b (* todo: masks should not be expressions *)
    | Expr_LitString(s) -> from_stringLit s
    )

(** Evaluate L-expression in write-mode (i.e., this is not a read-modify-write) *)
and eval_lexpr (loc: l) (env: Env.t) (x: AST.lexpr) (r: value): unit =
    ( match x with
    | LExpr_Wildcard ->
            ()
    | LExpr_Var(v) ->
            Env.setVar loc env v r
    | LExpr_Field(l, f) ->
            eval_lexpr_modify loc env l (fun prev -> set_field loc prev f r)
    | LExpr_Fields(l, fs) ->
            let rec set_fields (i: int) (fs: ident list) (prev: value): value =
                (match fs with
                | [] -> prev
                | (f::fs') ->
                        let p = get_field loc prev f in (* read previous value to get width *)
                        let w = Primops.prim_length_bits (Value.to_bits loc p) in
                        let y = extract_bits' loc r i w in
                        let v' = set_field loc prev f y in
                        set_fields (i + w) fs' v'
                )
            in
            eval_lexpr_modify loc env l (set_fields 0 fs)
    | LExpr_Slices(l, ss) ->
            let rec eval (o: value) (ss': AST.slice list) (prev: value): value =
                (match ss' with
                | [] -> prev
                | (s :: ss) ->
                        let (i, w) = eval_slice loc env s in
                        let v      = extract_bits'' loc r o w in
                        eval (eval_add_int loc o w) ss (insert_bits loc prev i w v)
                )
            in
            eval_lexpr_modify loc env l (eval (VInt Z.zero) (List.rev ss))
    | LExpr_BitTuple(ls) ->
            failwith "eval_lexpr: bittuple"
    | LExpr_Tuple(ls) ->
            let rs = of_tuple loc r in
            assert (List.length ls = List.length rs);
            List.iter2 (eval_lexpr loc env) ls rs
    | LExpr_Array(l, i) ->
            let i' = eval_expr loc env i in
            eval_lexpr_modify loc env l (fun prev -> set_array loc prev i' r)
    | LExpr_Write(setter, tes, es) ->
            let tvs = eval_exprs loc env tes in
            let vs  = eval_exprs loc env es in
            eval_proccall loc env setter tvs (List.append vs [r])
    | _ ->
            failwith ("eval_lexpr: "^ (pp_lexpr x))
    )

(** Evaluate L-expression in read-modify-write mode.

    1. The old value of the L-expression is read.
    2. The function 'modify' is applied to the old value
    3. The result is written back to the L-expression.
 *)
and eval_lexpr_modify (loc: l) (env: Env.t) (x: AST.lexpr) (modify: value -> value): unit =
    (match x with
    | LExpr_Var(v) ->
            Env.setVar loc env v (modify (Env.getVar loc env v))
    | LExpr_Field(l, f) ->
            let modify' (prev: value): value =
                let old = get_field loc prev f in
                set_field loc prev f (modify old)
            in
            eval_lexpr_modify loc env l modify'
    | LExpr_Array(l, i) ->
            let i' = eval_expr loc env i in
            let modify' (prev: value): value =
                let old = get_array loc prev i' in
                set_array loc prev i' (modify old)
            in
            eval_lexpr_modify loc env l modify'
    | LExpr_ReadWrite (getter, setter, tes, es) ->
            let tvs = eval_exprs loc env tes in
            let vs  = eval_exprs loc env es in
            let old = eval_funcall loc env getter tvs vs in
            eval_proccall loc env setter tvs (List.append vs [modify old])
    | _ ->
            failwith "eval_lexpr_modify"
    )

(** Evaluate list of statements *)
and eval_stmts (env: Env.t) (xs: AST.stmt list): unit =
    Env.nest (fun env' -> List.iter (eval_stmt env') xs) env

(** Evaluate statement *)
and eval_stmt (env: Env.t) (x: AST.stmt): unit =
    (match x with
    | Stmt_VarDeclsNoInit(ty, vs, loc) ->
            List.iter (fun v -> Env.addLocalVar loc env v (mk_uninitialized loc env ty)) vs
    | Stmt_VarDecl(ty, v, i, loc) ->
            let i' = eval_expr loc env i in
            Env.addLocalVar loc env v i'
    | Stmt_ConstDecl(ty, v, i, loc) ->
            let i' = eval_expr loc env i in
            Env.addLocalConst loc env v i'
    | Stmt_Assign(l, r, loc) ->
            let r' = eval_expr loc env r in
            eval_lexpr loc env l r'
    | Stmt_TCall(f, tes, es, loc) ->
            let tvs = eval_exprs loc env tes in
            let vs  = eval_exprs loc env es in
            eval_proccall loc env f tvs vs
    | Stmt_FunReturn(e, loc) ->
            let v = eval_expr loc env e in
            raise (Return (Some v))
    | Stmt_ProcReturn(loc) ->
            raise (Return None)
    | Stmt_Assert(e, loc) ->
            if not (to_bool loc (eval_expr loc env e)) then
                raise (EvalError (loc, "assertion failure"))
    | Stmt_Unpred(loc) ->
            raise (Throw (loc, Exc_Unpredictable))
    | Stmt_ConstrainedUnpred(loc) ->
            raise (Throw (loc, Exc_ConstrainedUnpredictable))
    | Stmt_ImpDef(v, loc) ->
            raise (Throw (loc, Exc_ImpDefined (pprint_ident v)))
    | Stmt_Undefined(loc) ->
            raise (Throw (loc, Exc_Undefined))
    | Stmt_ExceptionTaken(loc) ->
            raise (Throw (loc, Exc_ExceptionTaken))
    | Stmt_Dep_Unpred(loc) ->
            raise (Throw (loc, Exc_Unpredictable))
    | Stmt_Dep_ImpDef(s, loc) ->
            raise (Throw (loc, Exc_ImpDefined s))
    | Stmt_Dep_Undefined(loc) ->
            raise (Throw (loc, Exc_Undefined))
    | Stmt_See(e, loc) ->
            let s = to_string loc (eval_expr loc env e) in
            raise (Throw (loc, Exc_SEE s))
    | Stmt_Throw(v, loc) ->
            let ex = to_exc loc (Env.getVar loc env v) in
            raise (Throw ex)
    | Stmt_If(c, t, els, e, loc) ->
            let rec eval css d =
                (match css with
                | [] -> eval_stmts env d
                | (S_Elsif_Cond(c, s) :: css') ->
                        if to_bool loc (eval_expr loc env c) then
                            eval_stmts env s
                        else
                            eval css' d
                )
            in
            eval (S_Elsif_Cond(c, t) :: els) e
    | Stmt_Case(e, alts, odefault, loc) ->
            let rec eval v alts =
                (match alts with
                | [] ->
                        (match odefault with
                        | None -> raise (EvalError (loc, "unmatched case"))
                        | Some s -> eval_stmts env s
                        )
                | (Alt_Alt(ps, oc, s) :: alts') ->
                        if List.exists (eval_pattern loc env v) ps && from_option
                        (map_option (to_bool loc) (map_option (eval_expr loc env) oc)) (fun _ -> true) then
                            eval_stmts env s
                        else
                            eval v alts'
                )
            in
            eval (eval_expr loc env e) alts
    | Stmt_For(v, start, dir, stop, b, loc) ->
            let start' = eval_expr loc env start in
            let stop'  = eval_expr loc env stop in
            let rec eval i =
                let c = (match dir with
                | Direction_Up   -> eval_leq loc i stop'
                | Direction_Down -> eval_leq loc stop' i
                ) in
                if c then begin
                    Env.nest (fun env' ->
                        Env.addLocalVar loc env' v i;
                        eval_stmts env' b
                    ) env;
                    let i' = (match dir with
                    | Direction_Up   -> eval_add_int loc i (VInt Z.one)
                    | Direction_Down -> eval_sub_int loc i (VInt Z.one)
                    ) in
                    eval i'
                end
            in
            eval start'

    | Stmt_While(c, b, loc) ->
            let rec eval _ =
                if to_bool loc (eval_expr loc env c) then
                    eval_stmts env b;
                    eval ()
            in
            eval ()
    | Stmt_Repeat(b, c, loc) ->
            let rec eval _ =
                eval_stmts env b;
                if to_bool loc (eval_expr loc env c) then
                    eval ()
            in
            eval ()
    | Stmt_Try(tb, ev, catchers, odefault, loc) ->
            (try
                eval_stmts env tb
            with
            | Return v -> raise (Return v)
            | Throw (l, ex) ->
                Env.nest (fun env' ->
                    let rec eval cs =
                        (match cs with
                        | [] ->
                            (match odefault with
                            | None   -> raise (Throw (l, ex))
                            | Some s -> eval_stmts env' s
                            )
                        | (Catcher_Guarded(c, b) :: cs') ->
                            if to_bool loc (eval_expr loc env' c) then
                                eval_stmts env' b
                            else
                                eval cs'
                        )
                    in
                    Env.addLocalVar loc env' ev (VExc (l, ex));
                    eval catchers
                ) env
            )
    )

(** Evaluate call to function or procedure *)
and eval_call (loc: l) (env: Env.t) (f: ident) (tvs: value list) (vs: value list): unit =
    (match eval_prim (name_of_FIdent f) tvs vs with
    | Some r ->
        if !trace_primop then begin
            Printf.printf "TRACE primop: %s " (pprint_ident f);
            List.iter (fun v -> Printf.printf " [%s]" (pp_value v)) tvs;
            List.iter (fun v -> Printf.printf " %s" (pp_value v)) vs;
            Printf.printf " --> %s\n" (pp_value r);
        end;
        raise (Return (Some r))
    | None ->
        begin
            if !trace_funcall then begin
                Printf.printf "TRACE funcall: %s " (pprint_ident f);
                List.iter (fun v -> Printf.printf " [%s]" (pp_value v)) tvs;
                List.iter (fun v -> Printf.printf " %s" (pp_value v)) vs;
                Printf.printf "\n"
            end;
            let (targs, args, loc, b) = Env.getFun loc env f in
            assert (List.length targs = List.length tvs);
            assert (List.length args  = List.length vs);
            Env.nestTop (fun env' ->
                List.iter2 (fun arg v -> Env.addLocalVar loc env' arg v) targs tvs;
                List.iter2 (fun arg v -> Env.addLocalVar loc env' arg v) args vs;
                eval_stmts env' b
            ) env
        end
    )

(** Evaluate call to function *)
and eval_funcall (loc: l) (env: Env.t) (f: ident) (tvs: value list) (vs: value list): value =
    (try
        eval_call loc env f tvs vs;
        raise (EvalError (loc, "no return statement"))
    with
    | Return (Some v) -> v
    | Throw (l, ex) -> raise (Throw (l, ex))
    )

(** Evaluate call to procedure *)
and eval_proccall (loc: l) (env: Env.t) (f: ident) (tvs: value list) (vs: value list): unit =
    (try
        eval_call loc env f tvs vs
    with
    | Return None -> ()
    | Return (Some (VTuple [])) -> ()
    | Throw (l, ex) -> raise (Throw (l, ex))
    )

(** Evaluate instruction encoding *)
let eval_encoding (env: Env.t) (x: encoding) (op: value): bool =
    let Encoding_Block (nm, iset, fields, opcode, guard, unpreds, b, loc) = x in
    (* todo: consider checking iset *)
    (* Printf.printf "Checking opcode match %s == %s\n" (Utils.to_string (PP.pp_opcode_value opcode)) (pp_value op); *)
    let ok = (match opcode with
    | Opcode_Bits b -> eval_eq     loc op (from_bitsLit b)
    | Opcode_Mask m -> eval_inmask loc op (from_maskLit m)
    ) in
    if ok then begin
        if !trace_instruction then Printf.printf "TRACE: instruction %s\n" (pprint_ident nm);
        List.iter (function (IField_Field (f, lo, wd)) ->
            let v = extract_bits' loc op lo wd in
            if !trace_instruction then Printf.printf "      %s = %s\n" (pprint_ident f) (pp_value v);
            Env.addLocalVar loc env f v
        ) fields;
        if to_bool loc (eval_expr loc env guard) then begin
            List.iter (fun (i, b) ->
                if eval_eq loc (extract_bits' loc op i 1) (from_bitsLit b) then
                    raise (Throw (loc, Exc_Unpredictable))
            ) unpreds;
            List.iter (eval_stmt env) b;
            true
        end else begin
            false
        end
    end else begin
        false
    end

(** Evaluate bitslice of instruction opcode *)
let eval_decode_slice (loc: l) (env: Env.t) (x: decode_slice) (op: value): value =
    (match x with
    | DecoderSlice_Slice (lo, wd) -> extract_bits' loc op lo wd
    | DecoderSlice_FieldName f -> Env.getVar loc env f
    | DecoderSlice_Concat fs -> eval_concat loc (List.map (Env.getVar loc env) fs)
    )

(** Evaluate instruction decode pattern match *)
let rec eval_decode_pattern (loc: AST.l) (x: decode_pattern) (op: value): bool =
    (match x with
    | DecoderPattern_Bits     b -> eval_eq     loc op (from_bitsLit b)
    | DecoderPattern_Mask     m -> eval_inmask loc op (from_maskLit m)
    | DecoderPattern_Wildcard _ -> true
    | DecoderPattern_Not      p -> not (eval_decode_pattern loc p op)
    )

(** Evaluate instruction decode case alternative *)
let rec eval_decode_alt (loc: AST.l) (env: Env.t) (DecoderAlt_Alt (ps, b)) (vs: value list) (op: value): bool =
    if List.for_all2 (eval_decode_pattern loc) ps vs then
        (match b with
        | DecoderBody_UNPRED loc -> raise (Throw (loc, Exc_Unpredictable))
        | DecoderBody_UNALLOC loc -> raise (Throw (loc, Exc_Undefined))
        | DecoderBody_NOP loc -> true
        | DecoderBody_Encoding (enc, l) ->
                let (enc, opost, cond, exec) = Env.getInstruction loc env enc in
                if eval_encoding env enc op then begin
                    (match opost with
                    | Some post -> eval_stmts env post
                    | None -> ()
                    );
                    (* todo: should evaluate ConditionHolds to decide whether to execute body *)
                    List.iter (eval_stmt env) exec;
                    true
                end else begin
                    false
                end
        | DecoderBody_Decoder (fs, c, loc) ->
                let env = Env.empty in (* todo: this seems to share a single mutable object far too widely *)
                List.iter (function (IField_Field (f, lo, wd)) ->
                    Env.addLocalVar loc env f (extract_bits' loc op lo wd)
                ) fs;
                eval_decode_case loc env c op;
                true
        )
    else
        false

(** Evaluate instruction decode case *)
and eval_decode_case (loc: AST.l) (env: Env.t) (x: decode_case) (op: value): unit =
    (match x with
    | DecoderCase_Case (ss, alts, loc) ->
            let vs = List.map (fun s -> eval_decode_slice loc env s op) ss in
            let rec eval alts =
                (match alts with
                | (alt :: alts') ->
                        if eval_decode_alt loc env alt vs op then
                            ()
                        else
                            eval alts'
                | [] ->
                        raise (EvalError (loc, "unmatched decode pattern"))
                )
            in
            eval alts
    )


(****************************************************************)
(** {2 Creating environment from global declarations}           *)
(****************************************************************)

(* todo: it would be better to make this a distinct value *)
let eval_uninitialized (loc: l) (env: Env.t) (x: AST.ty): value = eval_unknown loc env x

(** Construct environment from global declarations *)
let build_evaluation_environment (ds: AST.declaration list): Env.t = begin
    if false then Printf.printf "Building environment from %d declarations\n" (List.length ds);
    let env = Env.empty in
    (* todo?: first pull out the constants/configs and evaluate all of them
     * lazily?
     *)
    List.iter (fun d ->
        (match d with
        | Decl_Record (v, fs, loc) ->
                Env.addRecord env v fs
        | Decl_Enum(qid, es, loc) ->
                let evs = if qid = Ident "boolean" then begin (* optimized special case *)
                              [ (Ident "FALSE", VBool false); (Ident "TRUE", VBool true) ]
                          end else begin
                              List.mapi (fun i e -> (e, VEnum (e, i))) es;
                          end
                in
                List.iter (fun (e, v) -> Env.addGlobalConst env e v) evs;
                Env.addEnum env qid (List.map (fun (e, v) -> v) evs)
        | Decl_Typedef (v, ty, loc) ->
                Env.addTypedef env v ty
        | Decl_Var(ty, v, loc) ->
                let init = eval_uninitialized loc env ty in
                Env.addGlobalVar env v init
        | Decl_Const(ty, v, i, loc) ->
                (* todo: constants need to be lazily evaluated or need to be
                 * sorted by dependencies
                 *)
                let init = eval_expr loc env i in
                Env.addGlobalConst env v init
        | Decl_FunDefn(rty, f, atys, body, loc) ->
                let tvs  = Asl_utils.to_sorted_list (TC.fv_funtype (f, false, [], [], atys, rty)) in
                let args = List.map snd atys in
                Env.addFun loc env f (tvs, args, loc, body)
        | Decl_ProcDefn(f, atys, body, loc) ->
                let tvs  = Asl_utils.to_sorted_list (Asl_utils.fv_args atys) in
                let args = List.map snd atys in
                Env.addFun loc env f (tvs, args, loc, body)
        | Decl_VarGetterDefn(ty, f, body, loc) ->
                let tvs  = Asl_utils.to_sorted_list (Asl_utils.fv_type ty) in
                let args = [] in
                Env.addFun loc env f (tvs, args, loc, body)
        | Decl_ArrayGetterDefn(rty, f, atys, body, loc) ->
                let tvs = Asl_utils.to_sorted_list (TC.fv_funtype (f, true, [], [], atys, rty)) in
                let args = List.map snd atys in
                Env.addFun loc env f (tvs, args, loc, body)
        | Decl_VarSetterDefn(f, ty, v, body, loc) ->
                let tvs  = Asl_utils.to_sorted_list (Asl_utils.fv_type ty) in
                let args = [v] in
                Env.addFun loc env f (tvs, args, loc, body)
        | Decl_ArraySetterDefn(f, atys, ty, v, body, loc) ->
                let tvs = Asl_utils.to_sorted_list (Asl_utils.IdentSet.union (Asl_utils.fv_sformals atys) (Asl_utils.fv_type ty)) in
                let name_of (x: AST.sformal): ident =
                    (match x with
                    | Formal_In (_, nm) -> nm
                    | Formal_InOut (_, nm) -> nm
                    )
                in
                let args = List.map name_of atys in
                Env.addFun loc env f (tvs, List.append args [v], loc, body)
        | Decl_InstructionDefn(nm, encs, opost, conditional, exec, loc) ->
                (* Instructions are looked up by their encoding name *)
                List.iter (fun enc ->
                    let Encoding_Block (nm, _, _, _, _, _, _, _) = enc in
                    Env.addInstruction loc env nm (enc, opost, conditional, exec)
                ) encs
        | Decl_DecoderDefn(nm, case, loc) ->
                Env.addDecoder env nm case
        | Decl_NewMapDefn(rty, f, atys, body, loc) ->
                let tvs  = Asl_utils.to_sorted_list (TC.fv_funtype (f, false, [], [], atys, rty)) in
                let args = List.map snd atys in
                Env.addFun loc env f (tvs, args, loc, body)
        (*
        | Decl_MapClause(f, atys, cond, body, loc) ->
                let tvs   = Asl_utils.to_sorted_list (Asl_utils.fv_args atys) in
                let args' = List.map snd args in
                Env.addFun loc env f (tvs, args', loc, body)
        *)
        | Decl_NewEventDefn (f, atys, loc) ->
                let tvs   = Asl_utils.to_sorted_list (Asl_utils.fv_args atys) in
                let args = List.map snd atys in
                Env.addFun loc env f (tvs, args, loc, [])
        | Decl_EventClause (f, body, loc) ->
                let (tvs, args, _, body0) = Env.getFun loc env f in
                Env.addFun loc env f (tvs, args, loc, List.append body body0)
        (* todo: when creating initial environment, should pass in a set of configuration
         * options that will override any default values given in definition
         *)
        | Decl_Config(ty, v, i, loc) ->
                (* todo: config constants need to be lazily evaluated or need to be
                 * sorted by dependencies
                 *)
                let init = eval_expr loc env i in
                Env.addGlobalConst env v init

        (* The following declarations have no impact on execution *)
        | Decl_BuiltinType (_, _)           | Decl_Forward (_, _)
        | Decl_BuiltinFunction (_, _, _, _)
        | Decl_FunType (_, _, _, _)         | Decl_ProcType (_, _, _)
        | Decl_VarGetterType (_, _, _)      | Decl_ArrayGetterType (_, _, _, _)
        | Decl_VarSetterType (_, _, _, _)   | Decl_ArraySetterType (_, _, _, _, _)
        | Decl_Operator1 (_, _, _)
        | Decl_Operator2 (_, _, _)
        | Decl_MapClause (_, _, _, _, _)
        -> ()
        )
    ) ds;
    env
end


(****************************************************************
 * End
 ****************************************************************)
