(****************************************************************
 * ASL typechecker
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** Type inference and checker for ASL language *)

module PE   = PPrintEngine
module PC   = PPrintCombinators
module PP   = Asl_parser_pp
module AST  = Asl_ast
module Visitor = Asl_visitor

open PE
open AST
open Utils
open Asl_utils
open Printf

let verbose = false


(****************************************************************)
(** {3 Exceptions thrown by typechecker}                        *)
(****************************************************************)

exception UnknownObject of (l * string * string)
exception DoesNotMatch  of (l * string * string * string)
exception IsNotA        of (l * string * string)
exception Ambiguous     of (l * string * string)
exception TypeError     of (l * string)
exception InternalError of (string) (* internal invariants have been broken *)


(****************************************************************)
(** {3 AST construction utilities}                              *)
(****************************************************************)

(* todo: given the function/procedure distinction, it is not clear
 * that we need type_unit
 *)
let type_unit    = Type_Tuple([])
let type_integer = Type_Constructor(Ident "integer")
let type_bool    = Type_Constructor(Ident "boolean")
let type_real    = Type_Constructor(Ident "real")
let type_string  = Type_Constructor(Ident "string")
let type_bits (n: expr) = Type_Bits(n)
let type_exn     = Type_Constructor(Ident "__Exception")

let type_bitsK (k: intLit): AST.ty = type_bits(Expr_LitInt(k))

(** Construct expression "eq_int(x, y)" *)
let mk_eq_int (x: AST.expr) (y: AST.expr): AST.expr =
    Expr_TApply (FIdent ("eq_int",0), [], [x; y])

(** Construct expression "add_int(x, y)" *)
let mk_add_int (x: AST.expr) (y: AST.expr): AST.expr =
    Expr_TApply (FIdent ("add_int",0), [], [x; y])

(** Construct expression "sub_int(x, y)" *)
let mk_sub_int (x: AST.expr) (y: AST.expr): AST.expr =
    Expr_TApply (FIdent ("sub_int",0), [], [x; y])

(** Construct expression "(0 + x1) + ... + xn" *)
let mk_add_ints (xs: AST.expr list): AST.expr =
    List.fold_left mk_add_int (Expr_LitInt "0") xs

let mk_concat_ty (x: AST.ty) (y: AST.ty): AST.ty =
    (match (x, y) with
    | (Type_Bits(e1), Type_Bits(e2)) ->
            type_bits (mk_add_int e1 e2)
    | _ ->
            Printf.printf "Can't concatenate types %s and %s\n" (pp_type x) (pp_type y);
            raise (InternalError "mk_concat_ty")
    )

let mk_concat_tys (xs: AST.ty list): AST.ty =
    List.fold_left mk_concat_ty (type_bitsK "0") xs

let slice_width (x: AST.slice): AST.expr =
    (match x with
    | Slice_Single(e) -> Expr_LitInt "1"
    | Slice_HiLo(hi, lo) -> mk_add_int (mk_sub_int hi lo) (Expr_LitInt "1")
    | Slice_LoWd(lo, wd) -> wd
    )

let slices_width (xs: AST.slice list): AST.expr =
    mk_add_ints (List.map slice_width xs)

let ixtype_basetype (ty: AST.ixtype): AST.ty =
    (match ty with
    | Index_Enum tc -> Type_Constructor tc
    | Index_Range _ -> type_integer
    )


(****************************************************************)
(** {3 Prettyprinting support}                                  *)
(****************************************************************)

(** Table of binary operators used for resugaring expressions when printing
    error messages.
 *)
let binop_table : AST.binop Bindings.t ref = ref Bindings.empty

let add_binop (op: binop) (x: ident): unit =
    binop_table := Bindings.add x op !binop_table

(** Very pretty print expression (resugaring expressions) *)
let ppp_expr (x: expr): string =
    pp_expr (resugar_expr !binop_table x)

(** Very pretty print type (resugaring expressions) *)
let ppp_type (x: AST.ty): string =
    pp_type (resugar_type !binop_table x)


(****************************************************************)
(** {2 Environment representing global and local objects}       *)
(****************************************************************)

type typedef
    = Type_Builtin of ident
    | Type_Forward
    | Type_Record of (ty * ident) list
    | Type_Enumeration of ident list
    | Type_Abbreviation of ty

let pp_typedef (x: typedef): string =
    (match x with
    | Type_Builtin t -> "builtin " ^ pprint_ident t
    | Type_Forward   -> "forward"
    | Type_Record fs -> "record { " ^ String.concat "; " (List.map (fun (ty, f) -> pp_type ty ^" "^ pprint_ident f) fs) ^ "}"
    | Type_Enumeration es -> "enumeration {" ^ String.concat ", " (List.map pprint_ident es) ^ "}"
    | Type_Abbreviation ty -> pp_type ty
    )

type funtype = (AST.ident * bool * AST.ident list * AST.expr list * (AST.ty * AST.ident) list * AST.ty)

let ft_id ((f, _, _, _, _, _): funtype): AST.ident = f

let pp_funtype ((f, isArr, tvs, cs, atys, rty): funtype): document =
    PP.pp_ident f
    ^^ string " :: " ^^
    (if tvs = [] then
        string ""
    else
        (string "∀ " ^^ (PC.separate (string ", ") (List.map PP.pp_ident tvs))
        ^^ string " . ")
    )
    ^^
    (if cs = [] then
        string ""
    else
        ((PC.separate (string ", ") (List.map PP.pp_expr cs))
        ^^ string " => "
        )
    )
    ^^ (if isArr then PC.brackets else PC.parens)
       (PC.separate (string ", ") (List.map PP.pp_formal atys))
    ^^ string " -> "
    ^^ PP.pp_ty rty

let fv_funtype ((_, _, tvs, _, atys, rty): funtype): IdentSet.t =
    (* todo: should final tvs list we generate exclude any variable names mentioned in atys?
     * This would let us think of the tvs as being implicit parameters that are
     * added by the type inference process and would mean that there would be no
     * possible way that the value parameter "N" and a type parameter "N" could
     * be different from each other.
     * This would be different from archex and would break down a bit the distinction
     * between type variables and value variables.
     *)
    IdentSet.union (IdentSet.of_list tvs) (IdentSet.union (fv_args atys) (fv_type rty))

(* type of setter function *)
type sfuntype = (AST.ident * AST.ident list * AST.expr list * AST.sformal list * AST.ty)

let sft_id ((f, _, _, _, _): sfuntype): AST.ident = f

let pp_sfuntype ((f, tvs, cs, atys, vty): sfuntype): document =
    PP.pp_ident f
    ^^ string " :: " ^^
    (if tvs = [] then
        string ""
    else
        (string "∀ " ^^ (PC.separate (string ", ") (List.map PP.pp_ident tvs))
        ^^ string " . ")
    )
    ^^
    (if cs = [] then
        string ""
    else
        ((PC.separate (string ", ") (List.map PP.pp_expr cs))
        ^^ string " => "
        )
    )
    ^^ PC.parens (PC.separate (string ", ") (List.map PP.pp_sformal atys))
    ^^ string " <- "
    ^^ PP.pp_ty vty

let sformal_var (x: sformal): AST.ident =
    ( match x with
    | Formal_In    (_, v) -> v
    | Formal_InOut (_, v) -> v
    )

let sformal_type (x: sformal): AST.ty =
    ( match x with
    | Formal_In    (ty, _) -> ty
    | Formal_InOut (ty, _) -> ty
    )

let formal_of_sformal (x: AST.sformal): (AST.ty * AST.ident) =
    ( match x with
    | Formal_In    (ty, v) -> (ty, v)
    | Formal_InOut (ty, v) -> (ty, v)
    )

let funtype_of_sfuntype ((f, tvs, cs, atys, vty): sfuntype): funtype =
    (f, true, tvs, cs, List.map formal_of_sformal atys, vty)

module Operator1 = struct
    type t = AST.unop
    let compare x y = Stdlib.compare x y
end

module Operators1 = Map.Make(Operator1)

module Operator2 = struct
    type t = AST.binop
    let compare x y = Stdlib.compare x y
end

module Operators2 = Map.Make(Operator2)


(****************************************************************)
(** {3 Global Environment (aka the Global Symbol Table)}        *)
(****************************************************************)

module GlobalEnv : sig
    type t
    val mkempty             : unit -> t
    val addType             : t -> AST.l -> AST.ident -> typedef -> unit
    val getType             : t -> AST.ident -> typedef option
    val isType              : t -> AST.ident -> bool
    val isTycon             : t -> AST.ident -> bool
    val isEnum              : t -> AST.ident -> bool
    val addFuns             : t -> AST.l -> AST.ident -> funtype list -> unit
    val getFuns             : t -> AST.ident -> funtype list
    val addSetterFuns       : t -> AST.ident -> sfuntype list -> unit
    val getSetterFun        : t -> AST.ident -> sfuntype list
    val addOperators1       : t -> AST.l -> AST.unop  -> funtype list -> unit
    val getOperators1       : t -> AST.l -> AST.unop  -> funtype list
    val addOperators2       : t -> AST.l -> AST.binop -> funtype list -> unit
    val getOperators2       : t -> AST.l -> AST.binop -> funtype list
    val addEncoding         : t -> AST.ident -> unit
    val isEncoding          : t -> AST.ident -> bool
    val addGlobalVar        : t -> AST.l -> AST.ident -> AST.ty -> bool -> unit
    val getGlobalVar        : t -> AST.ident -> AST.ty option
end = struct
    type t = {
        mutable types       : typedef Bindings.t;
        mutable functions   : (funtype list) Bindings.t;
        mutable setters     : (sfuntype list) Bindings.t;
        mutable operators1  : (funtype list) Operators1.t;
        mutable operators2  : (funtype list) Operators2.t;
        mutable encodings   : IdentSet.t;
        mutable globals     : AST.ty Bindings.t;
    }

    let mkempty _: t = {
        types       = Bindings.empty;
        functions   = Bindings.empty;
        setters     = Bindings.empty;
        operators1  = Operators1.empty;
        operators2  = Operators2.empty;
        encodings   = IdentSet.empty;
        globals     = Bindings.empty;
    }

    let addType (env: t) (loc: AST.l) (qid: AST.ident) (t: typedef): unit =
        (* Printf.printf "New type %s at %s\n" qid (pp_loc loc); *)
        let t' = (match (Bindings.find_opt qid env.types, t) with
            | (None,              _)            -> t
            | (Some Type_Forward, _)            -> t
            | (Some p,            Type_Forward) -> p
            | (Some p,            _) when p <> t ->
                    raise (DoesNotMatch (loc, "type definition", pp_typedef t, pp_typedef p))
            | _ -> t
        ) in
        env.types <- Bindings.add qid t' env.types

    let getType (env: t) (qid: AST.ident): typedef option =
        Bindings.find_opt qid env.types

    let isType  (env: t) (qid: AST.ident): bool = true (* todo *)
    let isTycon (env: t) (qid: AST.ident): bool = true (* todo *)
    let isEnum  (env: t) (qid: AST.ident): bool = true (* todo *)

    let addFuns (env: t) (loc: AST.l) (qid: AST.ident) (ftys: funtype list): unit =
        env.functions <- Bindings.add qid ftys env.functions

    let getFuns (env: t) (qid: AST.ident): funtype list =
        (match Bindings.find_opt qid env.functions with
        | None -> []
        | Some tys -> tys
        )

    let addSetterFuns (env: t) (qid: AST.ident) (ftys: sfuntype list): unit =
        env.setters <- Bindings.add qid ftys env.setters

    let getSetterFun (env: t) (qid: AST.ident): sfuntype list =
        (match Bindings.find_opt qid env.setters with
        | None -> []
        | Some tys -> tys
        )

    let addOperators1 (env: t) (loc: AST.l) (op: AST.unop) (funs: funtype list): unit =
        env.operators1 <- Operators1.update op (fun ov ->
            let old = from_option ov (fun _ -> []) in
            Some (List.append funs old)
        ) env.operators1

    let getOperators1 (env: t) (loc: AST.l) (op: AST.unop): funtype list =
        from_option (Operators1.find_opt op (env.operators1)) (fun _ -> [])

    let addOperators2 (env: t) (loc: AST.l) (op: AST.binop) (funs: funtype list): unit =
        List.iter (function fty -> add_binop op (ft_id fty)) funs;
        env.operators2 <- Operators2.update op (fun ov ->
            let old = from_option ov (fun _ -> []) in
            Some (List.append funs old)
        ) env.operators2

    let getOperators2 (env: t) (loc: AST.l) (op: AST.binop): funtype list =
        from_option (Operators2.find_opt op (env.operators2)) (fun _ -> [])

    let addEncoding (env: t) (qid: AST.ident): unit =
        env.encodings <- IdentSet.add qid env.encodings

    let isEncoding (env: t) (qid: AST.ident): bool =
        IdentSet.mem qid env.encodings

    let addGlobalVar (env: t) (loc: AST.l) (qid: AST.ident) (ty: AST.ty) (isConstant: bool): unit =
        (* Printf.printf "New %s %s at %s\n" (if isConstant then "constant" else "variable") qid (pp_loc loc); *)
        env.globals <- Bindings.add qid ty env.globals

    let getGlobalVar (env: t) (v: AST.ident): AST.ty option =
        (* Printf.printf "Looking for global variable %s\n" (pprint_ident v); *)
        Bindings.find_opt v env.globals
end

(** dereference typedef *)
let rec derefType (env: GlobalEnv.t) (ty: AST.ty): AST.ty =
    (match ty with
    | Type_Constructor tc
    | Type_App (tc, _) ->
        (match GlobalEnv.getType env tc with
        (* todo: instantiate with type parameters? *)
        | Some (Type_Abbreviation ty') -> derefType env ty'
        | _ -> ty
        )
    | _ -> ty
    )

(** compare index types *)
let cmp_ixtype (ty1: AST.ixtype) (ty2: AST.ixtype): bool =
    (match (ty1, ty2) with
    | (Index_Enum tc1, Index_Enum tc2) -> tc1 = tc2
    | (Index_Range _,  Index_Range _)  -> true
    | _ -> false
    )

(** structural match on two types - ignoring the dependent type part *)
(* todo: does not handle register<->bits coercions *)
let rec cmp_type (env: GlobalEnv.t) (ty1: AST.ty) (ty2: AST.ty): bool =
    (match (derefType env ty1, derefType env ty2) with
    | (Type_Constructor c1,       Type_Constructor c2)       -> c1 = c2
    | (Type_Bits(e1),             Type_Bits(e2))             -> true
    | (Type_App (c1, es1),        Type_App (c2, es2))        -> c1 = c2
    | (Type_OfExpr e1,            Type_OfExpr e2)            -> raise (InternalError "cmp_type: typeof")
    (* todo: this is equating the types, not subtyping them *)
    | (Type_Bits(e1),             Type_Register (w2, _))     -> true
    | (Type_Register (w1, _),     Type_Bits(e2))             -> true
    | (Type_Register (w1, _),     Type_Register (w2, _))     -> true
    | (Type_Array (ixty1, elty1), Type_Array (ixty2, elty2)) -> cmp_ixtype ixty1 ixty2 && cmp_type env elty1 elty2
    | (Type_Tuple tys1,           Type_Tuple tys2)           ->
         (List.length tys1 = List.length tys2) && List.for_all2 (cmp_type env) tys1 tys2
    | _ -> false
    )


(****************************************************************)
(** {3 Field typechecking support}                              *)
(****************************************************************)

(** Field accesses can be either record fields or fields of registers

    This type captures the information needed to typecheck either of these
    - a list of fieldname/type pairs for records
    - a list of fieldname/slice pairs for registers
 *)
type fieldtypes
    = FT_Record of (ty * ident) list
    | FT_Register of (AST.slice list * ident) list

(** Get fieldtype information for a record/register type *)
let rec typeFields (env: GlobalEnv.t) (loc: AST.l) (x: ty): fieldtypes =
    (match derefType env x with
    | Type_Constructor tc
    | Type_App (tc, _) ->
        (match GlobalEnv.getType env tc with
        | Some(Type_Record fs) -> FT_Record fs
        | Some(Type_Abbreviation ty') -> typeFields env loc ty'
        | _ -> raise (IsNotA(loc, "record", pprint_ident tc))
        )
    | Type_Register (wd, fs) -> FT_Register fs
    | Type_OfExpr(e) -> raise (InternalError ("typeFields: Type_OfExpr " ^ ppp_expr e))
    | _ -> raise (IsNotA(loc, "record/register", pp_type x))
    )

(** Get fieldtype information for a named field of a record *)
let get_recordfield (loc: AST.l) (rfs: (ty * ident) list) (f: ident): AST.ty =
    (match List.filter (fun (_, fnm) -> fnm = f) rfs with
    | [(fty, _)] -> fty
    | [] -> raise (UnknownObject(loc, "field", pprint_ident f))
    | fs -> raise (Ambiguous (loc, "field", pprint_ident f))
    )

(** Get fieldtype information for a named field of a slice *)
let get_regfield_info (loc: AST.l) (rfs: (AST.slice list * ident) list) (f: ident): AST.slice list =
    (match List.filter (fun (_, fnm) -> fnm = f) rfs with
    | [(ss, _)] -> ss
    | [] -> raise (UnknownObject(loc, "field", pprint_ident f))
    | fs -> raise (Ambiguous (loc, "field", pprint_ident f))
    )

(** Get named field of a register and calculate type *)
let get_regfield (loc: AST.l) (rfs: (AST.slice list * ident) list) (f: ident): (AST.slice list * AST.ty) =
    let ss = get_regfield_info loc rfs f in
    (ss, type_bits (slices_width ss))

(** Get named fields of a register and calculate type of concatenating them *)
let get_regfields (loc: AST.l) (rfs: (AST.slice list * ident) list) (fs: ident list): (AST.slice list * AST.ty) =
    let ss = List.flatten (List.map (get_regfield_info loc rfs) fs) in
    (ss, type_bits (slices_width ss))



(****************************************************************)
(** {3 Environment (aka the Local+Global Symbol Table)}         *)
(****************************************************************)

(* The handling of implicitly declared variables is complex.
 *
 * The typechecker inserts a variable declaration for any variable
 * that is assigned to for which there is no explicit declaration.
 *
 * To match the way that ASL is written, the declaration doesn't
 * always go in the current (i.e., innermost) scope because
 * a lot of ASL code requires that the variable should still
 * exist after the current scope has ended.
 *
 * At the same time, the declaration must:
 * - be legal: any variables used in the type of the declaration
 *   must be in scope
 * - mean the same: any variables used in the type of the declaration
 *   must have the same values
 * - be unique: there must be at most one declaration of each variable
 *   name (implicit or explicit) within a function
 *   (Note that this also means that we cannot explicitly declare two
 *   variables with the same name in different scopes - even if they have
 *   the same type.)
 *
 * So the rule for deciding where to put an implicit variable declaration is:
 * - it must occur before the initial assignment(s)
 * - there must be no assignment to any dependent variables between
 *   the declaration and the initial assignment(s)
 *
 * To implement this, the environment tracks:
 * - the set of all local variables (implicit or explicit) in this function
 * - the set of variables assigned to so far in each scope
 * - the list of pending implicit declarations waiting to be emitted
 *   (this is a list to make it easier to emit declarations in order)
 * And we maintain the invariant that none of the pending implicit declarations
 * have dependencies that are modified in the current (innermost) scope.
 *
 * New variables (both implicitly declared and explicitly declared) are
 * checked against the set of all local variables for conflicts.
 *
 * New implicitly declared variables either:
 * - have declarations inserted immediately before their assignment
 *   (if their type depends on variables modified in the current scope)
 * or
 * - are added to the list of implicit declarations
 *
 * On leaving scope I for scope O:
 * - explicit declarations are inserted for any pending implicit declarations that
 *   depend on variables modified in scope O
 *)

type implicitVars = (AST.ident * AST.ty) list

let declare_implicits (loc: AST.l) (imps: implicitVars): AST.stmt list =
    List.map (fun (v, ty) -> Stmt_VarDeclsNoInit(ty, [v], loc)) imps

module Env : sig
    type t
    val mkEnv               : GlobalEnv.t -> t
    val globals             : t -> GlobalEnv.t
    val nest                : (t -> 'a) -> (t -> 'a)
    val nest_with_bindings  : (t -> 'a) -> (t -> ('a * (AST.ident * AST.ty) list))
    val addLocalVar         : t -> AST.l -> AST.ident -> AST.ty -> unit
    val addLocalImplicitVar : t -> AST.l -> AST.ident -> AST.ty -> unit
    val getAllImplicits     : t -> implicitVars
    val getImplicits        : t -> implicitVars
    val getVar              : t -> AST.ident -> (AST.ident * AST.ty) option
    val markModified        : t -> AST.ident -> unit
    val addConstraint       : t -> AST.l -> AST.expr -> unit
    val getConstraints      : t -> AST.expr list
    val setReturnType       : t -> AST.ty -> unit
    val getReturnType       : t -> AST.ty option
end = struct
    type t = {
        globals             : GlobalEnv.t;
        mutable rty         : AST.ty option;

        (* a stack of nested scopes representing the local type environment *)
        (* Invariant: the stack is never empty *)
        mutable locals      : AST.ty Bindings.t list;
        mutable modified    : IdentSet.t;
        mutable implicits   : AST.ty Bindings.t ref;

        (* constraints collected while typechecking current expression/assignment *)
        mutable constraints : AST.expr list;
    }

    let mkEnv (globalEnv: GlobalEnv.t) = {
        globals     = globalEnv;
        rty         = None;
        locals      = [Bindings.empty];
        modified    = IdentSet.empty;
        implicits   = ref Bindings.empty;
        constraints = [];
    }

    (* todo: would it be better to make Env a subclass of GlobalEnv
     * Doing that would eliminate many, many calls to this function
     *)
    let globals (env: t): GlobalEnv.t =
        env.globals

    let nest (k: t -> 'a) (parent: t): 'a =
        let child = {
            globals     = parent.globals;
            rty         = parent.rty;
            locals      = Bindings.empty :: parent.locals;
            modified    = IdentSet.empty;
            implicits   = parent.implicits;
            constraints = parent.constraints;
        } in
        let r = k child in
        parent.modified <- IdentSet.union parent.modified child.modified;
        r

    let nest_with_bindings (k: t -> 'a) (parent: t): ('a * (AST.ident * AST.ty) list) =
        let child = {
            globals     = parent.globals;
            rty         = parent.rty;
            locals      = Bindings.empty :: parent.locals;
            modified    = IdentSet.empty;
            implicits   = parent.implicits;
            constraints = parent.constraints;
        } in
        let r = k child in
        parent.modified <- IdentSet.union parent.modified child.modified;
        let locals    = Bindings.bindings (List.hd child.locals) in
        (r, locals)

    let addLocalVar (env: t) (loc: AST.l) (v: AST.ident) (ty: AST.ty): unit =
        (* Printf.printf "New local var %s : %s at %s\n" (pprint_ident v) (ppp_type ty) (pp_loc loc); *)
        (match env.locals with
        | (bs :: bss) -> env.locals <- (Bindings.add v ty bs) :: bss
        | []          -> raise (InternalError "addLocalVar")
        );
        env.modified <- IdentSet.add v env.modified

    let addLocalImplicitVar (env: t) (loc: AST.l) (v: AST.ident) (ty: AST.ty): unit =
        (* Printf.printf "New implicit: %s : %s\n" (pprint_ident v) (ppp_type ty); *)
        env.implicits := Bindings.add v ty !(env.implicits);
        env.modified <- IdentSet.add v env.modified

    let getAllImplicits (env: t): implicitVars =
        let imps = !(env.implicits) in
        env.implicits := Bindings.empty;
        Bindings.bindings imps

    let getImplicits (env: t): implicitVars =
        let unconflicted _ (ty: AST.ty): bool =
            let deps = fv_type ty in
            IdentSet.disjoint deps env.modified
        in
        let (good, conflicts) = Bindings.partition unconflicted !(env.implicits) in
        env.implicits := good;
        Bindings.bindings conflicts

    let getVar (env: t) (v: AST.ident): (AST.ident * AST.ty) option =
        (* Printf.printf "Looking for variable %s\n" (pprint_ident v); *)
        let rec search (bss : AST.ty Bindings.t list): AST.ty option =
            (match bss with
            | (bs :: bss') ->
                    orelse_option (Bindings.find_opt v bs) (fun _ ->
                    search bss')
            | [] ->
                    orelse_option (Bindings.find_opt v !(env.implicits)) (fun _ ->
                    GlobalEnv.getGlobalVar env.globals v)
            )
        in
        map_option (fun ty -> (v, ty)) (search env.locals)

    let markModified (env: t) (v: AST.ident): unit =
        env.modified <- IdentSet.add v env.modified

    let addConstraint (env: t) (loc: AST.l) (c: AST.expr): unit =
        env.constraints <- c :: env.constraints

    let getConstraints (env: t): AST.expr list =
        env.constraints

    let setReturnType (env: t) (ty: AST.ty): unit =
        env.rty <- Some ty

    let getReturnType (env: t): AST.ty option =
        env.rty

end

(****************************************************************)
(** {2 Unification}                                             *)
(****************************************************************)

(****************************************************************)
(** {3 Expression simplification}                               *)
(****************************************************************)

(** Perform simple constant folding of expression

    It's primary role is to enable the 'DIV' hacks in
    z3_of_expr which rely on shallow syntactic transforms.
    It has a secondary benefit of sometimes causing constraints
    to become so trivial that we don't even need to invoke Z3
    which gives a performance benefit.
 *)

let rec simplify_expr (x: AST.expr): AST.expr =
    let eval (x: AST.expr): Big_int.big_int option =
        (match x with
        | Expr_LitInt x' -> Some (Big_int.big_int_of_string x')
        | _ -> None
        )
    in
    let to_expr (x: Big_int.big_int): AST.expr =
        Expr_LitInt (Big_int.string_of_big_int x)
    in

    (match x with
    | Expr_TApply (f, tes, es) ->
            let es' = List.map simplify_expr es in
            (match (f, flatten_map_option eval es') with
            | (FIdent ("add_int",_), Some [a; b]) -> to_expr (Big_int.add_big_int a b)
            | (FIdent ("sub_int",_), Some [a; b]) -> to_expr (Big_int.sub_big_int a b)
            | (FIdent ("mul_int",_), Some [a; b]) -> to_expr (Big_int.mult_big_int a b)
            | _ -> Expr_TApply (f, tes, es')
            )
    | _ -> x
    )

(** Perform simple constant folding of expressions within a type *)
let simplify_type (x: AST.ty): AST.ty =
    let repl = new replaceExprClass (fun e -> Some (simplify_expr e)) in
    Asl_visitor.visit_type repl x


(****************************************************************)
(** {3 Z3 support code}                                         *)
(****************************************************************)

(** Convert ASL expression to Z3 expression.
    This only copes with a limited set of operations: ==, +, -, * and DIV.
    (It is possible that we will need to extend this list in the future but
    it is sufficient for the current ASL specifications.)

    The support for DIV is not sound - it is a hack needed to cope with
    the way ASL code is written and generally needs a side condition
    that the division is exact (no remainder).

    ufs is a mutable list of conversions used to handle subexpressions
    that cannot be translated.  We treat such subexpressions as
    uninterpreted functions and add them to the 'ufs' list so that
    we can reason that "F(x) == F(x)" without knowing "F".
 *)

let rec z3_of_expr (ctx: Z3.context) (ufs: (AST.expr * Z3.Expr.expr) list ref) (x: AST.expr): Z3.Expr.expr =
    (match x with
    | Expr_Var(v) ->
        let intsort = Z3.Arithmetic.Integer.mk_sort ctx in
        Z3.Expr.mk_const_s ctx (pprint_ident v) intsort
    | Expr_Parens y -> z3_of_expr ctx ufs y
    | Expr_LitInt i -> Z3.Arithmetic.Integer.mk_numeral_s ctx i

    (* todo: the following lines involving DIV are not sound *)
    | Expr_TApply (FIdent ("mul_int",_), [], [Expr_TApply (FIdent ("fdiv_int",_), [], [a; b]); c]) when b = c -> z3_of_expr ctx ufs a
    | Expr_TApply (FIdent ("mul_int",_), [], [a; Expr_TApply (FIdent ("fdiv_int",_), [], [b; c])]) when a = c -> z3_of_expr ctx ufs b
    | Expr_TApply (FIdent ("add_int",_), [], [Expr_TApply (FIdent ("fdiv_int",_), [], [a1; b1]);
                                         Expr_TApply (FIdent ("fdiv_int",_), [], [a2; b2])])
         when a1 = a2 && b1 = b2 && b1 = Expr_LitInt "2"
         -> z3_of_expr ctx ufs a1
    | Expr_TApply (FIdent ("eq_int",_), [], [a; Expr_TApply (FIdent ("fdiv_int",_), [], [b; c])]) ->
            Z3.Boolean.mk_eq ctx
                (Z3.Arithmetic.mk_mul ctx [z3_of_expr ctx ufs c; z3_of_expr ctx ufs a])
                (z3_of_expr ctx ufs b)

    | Expr_TApply (FIdent ("add_int",_),  [], xs)    -> Z3.Arithmetic.mk_add ctx (List.map (z3_of_expr ctx ufs) xs)
    | Expr_TApply (FIdent ("sub_int",_),  [], xs)    -> Z3.Arithmetic.mk_sub ctx (List.map (z3_of_expr ctx ufs) xs)
    | Expr_TApply (FIdent ("mul_int",_),  [], xs)    -> Z3.Arithmetic.mk_mul ctx (List.map (z3_of_expr ctx ufs) xs)
    | Expr_TApply (FIdent ("fdiv_int",_), [], [a;b]) -> Z3.Arithmetic.mk_div ctx (z3_of_expr ctx ufs a) (z3_of_expr ctx ufs b)
    | Expr_TApply (FIdent ("eq_int",_),   [], [a;b]) -> Z3.Boolean.mk_eq ctx (z3_of_expr ctx ufs a) (z3_of_expr ctx ufs b)
    | _ ->
            if verbose then Printf.printf "    Unable to translate %s - using as uninterpreted function\n" (pp_expr x);
            let intsort = Z3.Arithmetic.Integer.mk_sort ctx in
            (match List.assoc_opt x !ufs with
            | None ->
                    let uf = Z3.Expr.mk_fresh_const ctx "UNINTERPRETED" intsort in
                    ufs := (x, uf) :: !ufs;
                    uf
            | Some uf ->
                    uf
            )
    )

(** check that bs => cs *)
let check_constraints (bs: expr list) (cs: expr list): bool =
    (* note that we rebuild the Z3 context each time.
     * It is possible to share them across all invocations to save
     * about 10% of execution time.
     *)
    let z3_ctx = Z3.mk_context [] in
    let solver = Z3.Solver.mk_simple_solver z3_ctx in
    let ufs = ref [] in (* uninterpreted function list *)
    let bs' = List.map (z3_of_expr z3_ctx ufs) bs in
    let cs' = List.map (z3_of_expr z3_ctx ufs) cs in
    let p = Z3.Boolean.mk_implies z3_ctx (Z3.Boolean.mk_and z3_ctx bs') (Z3.Boolean.mk_and z3_ctx cs') in
    if verbose then Printf.printf "      - Checking %s\n" (Z3.Expr.to_string p);
    Z3.Solver.add solver [Z3.Boolean.mk_not z3_ctx p];
    let q = Z3.Solver.check solver [] in
    if q = SATISFIABLE then Printf.printf "Failed property %s\n" (Z3.Expr.to_string p);
    q = UNSATISFIABLE


(****************************************************************)
(** {3 Unification support code}                                *)
(****************************************************************)

(** Unifier

    This class supports collecting all the constraints introduced while
    typechecking an expression, checking those constraints
    and synthesizing a solution.

    This is the most complex part of the entire typechecker.
    Most of that complexity is the result of having to support
    code like

        bits(64) x = ZeroExtend(R[i]);

    where the width of the ZeroExtend call is determined by
    the context that it occurs in.
 *)
class unifier (loc: AST.l) (assumptions: expr list) = object (self)

    (* unification results in bindings of the form "$i == $j".
     * We use a renaming structure to track equivalence classes
     * and to pick a canonical member of each equivalence class
     *)
    val mutable renamings = new equivalences

    val mutable bindings : AST.expr Bindings.t = Bindings.empty

    val mutable constraints : AST.expr list = []

    val mutable next = 0

    method fresh: ident =
        let v = genericTyvar next in
        ignore (renamings#canonicalize v); (* add v to rename table *)
        next  <- next + 1;
        v

    method isFresh (x: ident): bool =
        isGenericTyvar x

    method addEquality (x: AST.expr) (y: AST.expr): unit =
        (match (x, y) with
        | (Expr_Var v, Expr_Var w) when self#isFresh v && self#isFresh w ->
                renamings#merge v w
        | (Expr_Var v, _) when self#isFresh v && not (Bindings.mem v bindings) ->
                bindings <- Bindings.add v y bindings
        | (_, Expr_Var w) when self#isFresh w && not (Bindings.mem w bindings) ->
                bindings <- Bindings.add w x bindings
        | _ ->
                constraints <- mk_eq_int x y :: constraints
        )

    method addEqualities (xs: AST.expr list) (ys: AST.expr list) =
        if List.length xs = List.length ys then
            List.iter2 self#addEquality xs ys

    method checkConstraints: expr Bindings.t = begin
        (* Plan:
         * - Generate renaming that maps each fresh var to canonical
         *   representative of equivalence class.
         * - Collect all the bindings associated with each equivalence class.
         * - For each equivalence class, check that there is at least
         *   one closed binding for that equivalence class and
         *   add all the others as constraints.
         *   (A "closed binding" is a binding that does not contain any fresh
         *   variables - construct it by substituting other closed bindings
         *   into a binding.)
         * - If any equivalence class has no closed bindings, report an error.
         *)
        let rns     = renamings#mapping in
        let classes = renamings#classes in

        (* map each canonical representative to set of bindings *)
        let binds   = Bindings.map (fun vs -> flatmap_option (fun v -> Bindings.find_opt v bindings) (IdentSet.elements vs)) classes in

        if verbose then begin
            Printf.printf "    - Checking Constraints at %s\n" (pp_loc loc);
            Bindings.iter (fun v e -> Printf.printf "      Old Bind: %s -> %s\n" (pprint_ident v) (ppp_expr e)) bindings;
            Bindings.iter (fun v es -> List.iter (fun e -> Printf.printf "      binds: %s -> %s\n" (pprint_ident v) (ppp_expr e)) es) binds;
            renamings#pp "      Renaming: ";
            Bindings.iter (fun v w -> Printf.printf "      - renaming: %s -> %s\n" (pprint_ident v) (pprint_ident w)) rns
        end;

        let isClosed (x: expr): bool =
            IdentSet.is_empty (IdentSet.filter self#isFresh (fv_expr x))
        in

        (* todo: memoize close_ident to improve performance  - should probably profile first *)
        (* search for a closed binding for a variable x by testing whether any of the available bindings can be closed *)
        let rec close_ident (x: ident): expr =
            let x' = renamings#canonicalize x in
            (match bind_option (Bindings.find_opt x' binds) (fun es -> first_option close_expr es) with
            | Some e -> e
            | None ->
                Printf.printf "Type Error at %s\n" (pp_loc loc);
                if verbose then begin
                    List.iter (fun v -> Printf.printf "  Related to: %s\n" (pprint_ident v)) (IdentSet.elements (Bindings.find x' classes));
                    List.iter (fun e -> Printf.printf "  Candidate: %s\n" (pp_expr e)) (Bindings.find x' binds);
                    renamings#pp "  Renaming: ";
                    Bindings.iter (fun v e -> Printf.printf "  Bind: %s -> %s\n" (pprint_ident v) (ppp_expr e)) bindings
                end;
                raise (TypeError (loc, "Unable to infer value of type parameter "^ pprint_ident x'))
            )

            (* attempt to close an expression by replacing all fresh vars with a closed expression *)
        and close_expr (x: expr): expr option =
            let subst = new substFunClass (fun x -> if self#isFresh x then Some (close_ident x) else None) in
            let x'    = Asl_visitor.visit_expr subst x in
            if isClosed x' then
                Some x'
            else
                None
        in

        (* map of each canonical member to a closed expression *)
        let pre_closed = Bindings.mapi (fun k _ -> close_ident k) classes in


        (* extend map to all type variables *)
        let closed = Bindings.map (fun v -> Bindings.find v pre_closed) rns in

        if verbose then begin
            Bindings.iter (fun v e -> Printf.printf "      PreClosed Bind: %s -> %s\n" (pprint_ident v) (ppp_expr e)) pre_closed;
            Bindings.iter (fun v e -> Printf.printf "      Closed Bind: %s -> %s\n" (pprint_ident v) (ppp_expr e)) closed
        end;

        constraints <- List.map (subst_expr closed) constraints;

        (* turn all old bindings into constraints *)
        let new_constraints = List.map (fun (v, e) -> mk_eq_int (Bindings.find v closed) (subst_expr closed e)) (Bindings.bindings bindings) in
        constraints <- new_constraints @ constraints;
        bindings    <- closed;

        if verbose then begin
            List.iter (fun c -> Printf.printf "      OldConstraint: %s\n" (ppp_expr c)) constraints;
            List.iter (fun c -> Printf.printf "      NewConstraint: %s\n" (ppp_expr c)) new_constraints;
            List.iter (fun c -> Printf.printf "      Constraint: %s\n" (ppp_expr c)) constraints
        end;

        constraints <- List.map simplify_expr constraints;

        (* as a minor optimisation and also to declutter error messages, delete equalities that are obviously satisfied *)
        constraints <- List.filter (function Expr_TApply(FIdent ("eq_int",_), [], [x; y]) -> x <> y | _ -> true) constraints;

        (* The optimisation of not invoking solver if there are no constraints
         * improves runtime by a factor of 6x
         *)
        if constraints <> [] && not (check_constraints assumptions constraints) then begin
            Printf.printf "Type Error at %s\n" (pp_loc loc);
            if verbose then begin
                renamings#pp "      Renaming: ";
                Bindings.iter (fun v e -> Printf.printf "      Bind: %s -> %s\n" (pprint_ident v) (ppp_expr e)) bindings
            end;
            List.iter (fun c -> Printf.printf "      Constraint: %s\n" (ppp_expr c)) constraints;
            flush stdout;
            raise (TypeError (loc, "Type mismatch"))
        end;

        bindings
    end

end

(** Create a fresh unifier, invoke a function that uses the unifier and check
    that the constraints are satisfied.
    Returns the synthesized bindings and result of function
 *)
let with_unify (env: Env.t) (loc: AST.l) (f: unifier -> 'a): (expr Bindings.t * 'a) =
    let u = new unifier loc (Env.getConstraints env) in
    let r = f u in
    let bs = u#checkConstraints in
    (bs, r)

(****************************************************************)
(** {3 Type Unification}                                        *)
(****************************************************************)

(** Notes on how type inference works:

    - we use structural matching (ignoring the dependent type)
      to disambiguate each binop/unop/function/procedure call/getter/setter

    - as we construct each TApply node,
      - we insert fresh type variables $0, $1, ... for each of the type arguments
        (these are things we are going to solve for)
      - unification generates two kinds of constraints:
        1. bindings for type variables whenever unification requires "$i == e" or "e == $i"
           for some type variable $i
        2. constraints where there are multiple bindings for a single variable
        3. constraints on type variables whenever unification requires "e1 == e2"
           where e1 is not a variable

    - after scanning an entire assignment/expression, we check:
        1. do we have at least one binding for each variable?
        2. are the bindings consistent with the constraints?
      Note that we could potentially give better (more localized) type errors if
      we check for consistency as we go along and if we check that a variable
      is bound as soon as the result type could not possibly involve the variable.
      (e.g., when checking "(e1 == e2 && Q) || R", any type variables associated
      with the equality check do not impact the && or || because "boolean" does
      not have any type parameters.)

    Note that there is a choice of what type arguments to add to a function

        bits(N) ZeroExtend(bits(M) x, integer N)

    We can either:
    - add only the missing information "M"
      In effect, we are saying that missing type parameters are implicit parameters that are
      added by the type inference process and that the "type parameters" are basically just
      value expressions that are added by type inference.
    - add type arguments for both "M" and "N".
      In effect we are saying that type parameters are distinct from value parameters
      and we are in the strange situation that a function could have both a value
      parameter M and a type parameter N and they might be bound to different (but
      equivalent) arguments.
      This is what archex does.
 *)

(** Unify two index types *)
let unify_ixtype (u: unifier) (ty1: AST.ixtype) (ty2: AST.ixtype): unit =
    (match (ty1, ty2) with
    | (Index_Enum tc1,         Index_Enum tc2) -> ()
    | (Index_Range (lo1, hi1), Index_Range (lo2, hi2)) ->
            u#addEquality lo1 lo2;
            u#addEquality hi1 hi2
    | _ -> ()
    )

(** Unify two types

    This performs a structural match on two types - ignoring the dependent type part
 *)
(* todo: does not handle register<->bits coercions *)
let rec unify_type (env: GlobalEnv.t) (u: unifier) (ty1: AST.ty) (ty2: AST.ty): unit =
    (match (derefType env ty1, derefType env ty2) with
    | (Type_Constructor c1,       Type_Constructor c2)       -> ()
    | (Type_Bits(e1),             Type_Bits(e2))             -> u#addEquality e1 e2
    | (Type_App (c1, es1),        Type_App (c2, es2))        -> u#addEqualities es1 es2
    | (Type_OfExpr e1,            Type_OfExpr e2)            -> raise (InternalError "unify_type: typeof")
    (* todo: this is equating the types, not subtyping them *)
    | (Type_Bits(e1),             Type_Register (w2, _))     -> u#addEquality e1 (Expr_LitInt w2)
    | (Type_Register (w1, _),     Type_Bits(e2))             -> u#addEquality (Expr_LitInt w1) e2
    | (Type_Register (w1, _),     Type_Register (w2, _))     -> u#addEquality (Expr_LitInt w1) (Expr_LitInt w2)
    | (Type_Array (ixty1, elty1), Type_Array (ixty2, elty2)) -> unify_ixtype u ixty1 ixty2; unify_type env u elty1 elty2
    | (Type_Tuple tys1,           Type_Tuple tys2)           -> List.iter2 (unify_type env u) tys1 tys2
    | _ -> ()
    )

(** Apply substitutions to an expression *)
let unify_subst_e (s: expr Bindings.t) (x: AST.expr): AST.expr =
    subst_expr s x

(** Apply substitutions to an L-expression *)
let unify_subst_le (s: expr Bindings.t) (x: AST.lexpr): AST.lexpr =
    subst_lexpr s x

(** Apply substitutions to a type *)
let unify_subst_ty (s: expr Bindings.t) (x: AST.ty): AST.ty =
    subst_type s x

(** Replace all type variables in function type with fresh variables *)
let mkfresh_funtype (u: unifier) (fty: funtype): funtype =
    let (f, isArr, tvs, cs, atys, rty) = fty in

    (* generate renamings for all type variables *)
    let rns = List.map (fun tv -> (tv, u#fresh)) tvs in
    let s   = mk_bindings (List.map (fun (v, w) -> (v, Expr_Var w)) rns) in

    let tvs'  = List.map snd rns in
    let atys' = List.map (fun (ty, a) ->
        let ty' = subst_type s ty in
        let a'  = from_option (List.assoc_opt a rns) (fun _ -> a) in
        (ty', a')
    ) atys in
    let cs'   = List.map (subst_expr s) cs in
    let rty'  = subst_type s rty in
    (f, isArr, tvs', cs', atys', rty')

(** Replace all type variables in setter function type with fresh variables *)
let mkfresh_sfuntype (u: unifier) (fty: sfuntype): sfuntype =
    let (f, tvs, cs, atys, vty) = fty in

    (* generate renamings for all type variables *)
    let rns = List.map (fun tv -> (tv, u#fresh)) tvs in
    let s   = mk_bindings (List.map (fun (v, w) -> (v, Expr_Var w)) rns) in

    let tvs'  = List.map snd rns in
    let atys' = List.map (fun aty ->
        (match aty with
        | Formal_In(ty, a) ->
            let ty' = subst_type s ty in
            let a'  = from_option (List.assoc_opt a rns) (fun _ -> a) in
            Formal_In(ty', a')
        | Formal_InOut(ty, a) ->
            let ty' = subst_type s ty in
            let a'  = from_option (List.assoc_opt a rns) (fun _ -> a) in
            Formal_InOut(ty', a')
        )
    ) atys in
    let cs'   = List.map (subst_expr s) cs in
    let vty'  = subst_type s vty in
    (f, tvs', cs', atys', vty')

(** Check that ty2 is a subtype of ty1: ty1 >= ty2 *)
let check_type (env: Env.t) (u: unifier) (loc: AST.l) (ty1: AST.ty) (ty2: AST.ty): unit =
    if not (cmp_type (Env.globals env) ty1 ty2) then
        raise (DoesNotMatch(loc, "type", pp_type ty1, pp_type ty2))
    else
        unify_type (Env.globals env) u ty1 ty2

(** Check that ty1 is identical to ty2 *)
(* todo: make sure that this does not do subtyping *)
let check_type_exact (env: Env.t) (loc: AST.l) (ty1: AST.ty) (ty2: AST.ty): unit =
    ignore (with_unify env loc (fun u ->
        check_type env u loc ty1 ty2
    ))


(****************************************************************)
(** {2 Disambiguation of functions and operators}               *)
(****************************************************************)

(** Generate error message when function disambiguation fails *)
let reportChoices (loc: AST.l) (what: string) (nm: string) (tys: AST.ty list) (funs: funtype list): unit =
    if funs = [] then
        Printf.printf "%s: Can't find matching %s for %s\n" (pp_loc loc) what nm
    else
        Printf.printf "%s: Ambiguous choice for %s %s\n" (pp_loc loc) what nm;
    List.iter (fun ty -> Printf.printf "  Arg : %s\n" (pp_type ty)) tys;
    List.iter (fun (f, _, _, _, atys, rty) ->
        Printf.printf "  Choice : %s : %s -> %s\n"
            (pprint_ident f)
            (Utils.to_string (PPrintCombinators.separate (PPrintEngine.string " ")
                (List.map (fun (ty, _) -> PP.pp_ty ty) atys)))
            (pp_type rty)
    ) funs

(** Check whether a list of function argument types is compatible with the
    type of a function.

    One function type is compatible with another if they have the same number
    of arguments and each argument has the same base type
 *)
let isCompatibleFunction (env: GlobalEnv.t) (isArr: bool) (tys: AST.ty list) (ft: funtype): bool =
    let nargs = List.length tys in
    let (_, isArr', _, _, atys, _) = ft in
    isArr = isArr' && List.length atys = nargs && List.for_all2 (cmp_type env) (List.map fst atys) tys

(** Disambiguate a function name based on the number and type of arguments *)
let chooseFunction (env: GlobalEnv.t) (loc: AST.l) (what: string) (nm: string) (isArr: bool) (tys: AST.ty list) (funs: funtype list): funtype option =
    let funs' = List.filter (isCompatibleFunction env isArr tys) funs in
    (match nub funs' with
    | []  -> None
    | [r] -> Some r
    | fs  ->
            (* todo: it would probably be better to detect ambiguity when functions are
             * defined instead of waiting until they are called
             *)
            reportChoices loc what nm tys fs;
            raise (Ambiguous (loc, what, nm))
    )

(** Check whether a list of function argument types is compatible with the
    type of a setter function.

    One function type is compatible with another if they have the same number
    of arguments and each argument has the same base type
 *)
let isCompatibleSetterFunction (env: GlobalEnv.t) (tys: AST.ty list) (ft: sfuntype): bool =
    let nargs = List.length tys in
    let (_, _, _, atys, _) = ft in
    (List.length atys = nargs) && List.for_all2 (cmp_type env) (List.map sformal_type atys) tys

(** Disambiguate a setter function name based on the number and type of arguments *)
let chooseSetterFunction (env: GlobalEnv.t) (loc: AST.l) (what: string) (nm: ident) (tys: AST.ty list) (funs: sfuntype list): sfuntype option =
    let funs' = List.filter (isCompatibleSetterFunction env tys) funs in
    (match nub funs' with
    | []  -> None
    | [r] -> Some r
    | fs  ->
            (* todo: it would probably be better to detect ambiguity when functions are
             * defined instead of waiting until they are called
             *)
            reportChoices loc what (pprint_ident nm) tys (List.map funtype_of_sfuntype fs);
            raise (Ambiguous (loc, what, pprint_ident nm))
    )

(** Instantiate type of function using unifier 'u' *)
let instantiate_fun (env: GlobalEnv.t) (u: unifier) (loc: AST.l) (fty: funtype) (es: AST.expr list) (tys: AST.ty list): (AST.ident * AST.expr list * AST.ty) =
    let (f, _, tvs, cs, atys, rty) = mkfresh_funtype u fty in

    (* Add bindings for every explicit type argument *)
    assert ((List.length atys) == (List.length es));
    List.iter2 (fun (_, v) e -> if List.mem v tvs then u#addEquality (Expr_Var v) e) atys es;

    (* unify argument types *)
    assert ((List.length atys) == (List.length tys));
    List.iter2 (unify_type env u) (List.map fst atys) tys;

    let tes = List.map (fun tv -> Expr_Var tv) tvs in
    (f, tes, rty)

(** Instantiate type of setter function using unifier 'u' *)
let instantiate_sfun (env: GlobalEnv.t) (u: unifier) (loc: AST.l) (fty: sfuntype) (es: AST.expr list) (tys: AST.ty list) (ty: AST.ty): (AST.ident * AST.expr list) =
    let (f, tvs, cs, atys, vty) = mkfresh_sfuntype u fty in

    (* Add bindings for every explicit type argument *)
    assert ((List.length atys) == (List.length es));
    List.iter2 (fun aty e ->
        let v = sformal_var aty in
        if List.mem v tvs then u#addEquality (Expr_Var v) e
    ) atys es;

    (* unify argument types *)
    List.iter2 (unify_type env u) (List.map sformal_type atys) tys;

    (* unify value type *)
    unify_type env u vty ty;

    let tes = List.map (fun tv -> Expr_Var tv) tvs in
    (f, tes)


(** Disambiguate and typecheck application of a function to a list of arguments *)
let tc_apply (env: GlobalEnv.t) (u: unifier) (loc: AST.l) (what: string) (f: AST.ident) (es: AST.expr list) (tys: AST.ty list): (AST.ident * AST.expr list * AST.ty) =
    let funs  = GlobalEnv.getFuns env f in
    let nm    = pprint_ident f in
    (match chooseFunction env loc "function" nm false tys funs with
    | None ->
            reportChoices loc what nm tys funs;
            raise (UnknownObject(loc, what, nm))
    | Some fty ->
            if verbose then Printf.printf "    - Found matching %s at %s for %s = %s\n" what (pp_loc loc) nm (Utils.to_string (pp_funtype fty));
            instantiate_fun env u loc fty es tys
    )

(** Disambiguate and typecheck application of a unary operator to argument *)
let tc_unop (env: GlobalEnv.t) (u: unifier) (loc: AST.l) (op: unop) (x: AST.expr) (ty: AST.ty): (AST.ident * AST.expr list * AST.ty) =
    let what = "unary operator" in
    let nm   = Utils.to_string (PP.pp_unop op) in
    let tys  = [ty] in
    let ops  = GlobalEnv.getOperators1 env loc op in
    (match chooseFunction env loc what nm false [ty] ops with
    | None ->
            reportChoices loc what nm tys ops;
            raise (UnknownObject(loc, what, nm))
    | Some fty ->
            instantiate_fun env u loc fty [x] tys
    )

(** Disambiguate and typecheck application of a binary operator to arguments *)
let tc_binop (env: GlobalEnv.t) (u: unifier) (loc: AST.l) (op: binop) (x1: AST.expr) (x2: AST.expr) (ty1: AST.ty) (ty2: AST.ty): (AST.ident * AST.expr list * AST.ty) =
    let what = "binary operator" in
    let nm   = Utils.to_string (PP.pp_binop op) in
    let tys  = [ty1; ty2] in
    let ops  = GlobalEnv.getOperators2 env loc op in
    (match chooseFunction env loc what nm false tys ops with
    | None ->
            reportChoices loc "binary operator" nm tys ops;
            raise (UnknownObject(loc, what, nm))
    | Some fty ->
            instantiate_fun env u loc fty [x1; x2] tys
    )


(****************************************************************)
(** {2 Typecheck expressions}                                   *)
(****************************************************************)

(** Lookup a variable in environment *)
let check_var (env: Env.t) (loc: AST.l) (v: AST.ident): (AST.ident * AST.ty) =
    (match Env.getVar env v with
    | None -> raise (UnknownObject(loc, "variable", pprint_ident v))
    | Some (v', ty') -> (v', ty')
    )

(** Typecheck list of expressions *)
let rec tc_exprs (env: Env.t) (u: unifier) (loc: AST.l) (xs: AST.expr list): (AST.expr * AST.ty) list =
    List.map (tc_expr env u loc) xs

(** Typecheck expression and check that it is a subtype of ty *)
and check_expr (env: Env.t) (loc: AST.l) (ty: AST.ty) (x: AST.expr): AST.expr =
    let (s, x') = with_unify env loc (fun u ->
        let (x', ty') = tc_expr env u loc x in
        if verbose then Printf.printf "    - Typechecking %s : %s\n" (pp_expr x') (pp_type ty');
        check_type env u loc ty ty';
        x'
    ) in
    unify_subst_e s x'

(** Typecheck 'if c then expr' *)
and tc_e_elsif (env: Env.t) (u: unifier) (loc: AST.l) (x: AST.e_elsif): (AST.e_elsif * AST.ty) =
    (match x with
    | E_Elsif_Cond(c, e) ->
            let c'       = check_expr env loc type_bool c in
            let (e', ty) = tc_expr env u loc e in
            (E_Elsif_Cond(c', e'), ty)
    )

(** Typecheck bitslice indices *)
and tc_slice (env: Env.t) (u: unifier) (loc: AST.l) (x: AST.slice): (AST.slice * AST.ty) =
    (match x with
    | Slice_Single(e) ->
            let (e', ty) = tc_expr env u loc e in
            (Slice_Single(e'), ty)
    | Slice_HiLo(hi, lo) ->
            let hi' = check_expr env loc type_integer hi in
            let lo' = check_expr env loc type_integer lo in
            (Slice_HiLo(hi', lo'), type_integer)
    | Slice_LoWd(lo, wd) ->
            let lo' = check_expr env loc type_integer lo in
            let wd' = check_expr env loc type_integer wd in
            (Slice_LoWd(lo', wd'), type_integer)
    )

(** Typecheck pattern against type ty *)
and tc_pattern (env: Env.t) (loc: AST.l) (ty: AST.ty) (x: AST.pattern): AST.pattern = 
    ( match x with
    | Pat_LitInt(l) ->
            check_type_exact env loc ty type_integer;
            Pat_LitInt(l)
    | Pat_LitHex(l) ->
            check_type_exact env loc ty type_integer;
            Pat_LitHex(l)
    | Pat_LitBits(l) ->
            check_type_exact env loc ty (type_bitsK (string_of_int (masklength l)));
            Pat_LitBits(l)
    | Pat_LitMask(l) ->
            check_type_exact env loc ty (type_bitsK (string_of_int (masklength l)));
            Pat_LitMask(l)
    | Pat_Const(l) ->
            let (c, cty) = check_var env loc l in
            (* todo: check it is a global constant *)
            check_type_exact env loc ty cty;
            Pat_Const(c)
    | Pat_Wildcard ->
            Pat_Wildcard
    | Pat_Tuple(ps) ->
            let ps' = (match ty with
                | Type_Tuple tys when List.length ps = List.length tys ->
                    List.map2 (tc_pattern env loc) tys ps
                | _ -> raise (IsNotA(loc, "tuple of length ?", pp_type ty))
            ) in
            Pat_Tuple(ps')
    | Pat_Set(ps) ->
            let ps' = List.map (tc_pattern env loc ty) ps in
            Pat_Set(ps')
    | Pat_Single(Expr_LitMask m) ->
            (* todo: this is a workaround for bad IN sugar *)
            tc_pattern env loc ty (Pat_LitMask m)
    | Pat_Single(e) ->
            let e' = check_expr env loc ty e in
            Pat_Single(e')
    | Pat_Range(lo, hi) ->
            let lo' = check_expr env loc ty lo in
            let hi' = check_expr env loc ty hi in
            (* Must be integer because no other type supports <= operator *)
            check_type_exact env loc ty type_integer;
            Pat_Range(lo', hi')
    )

(** Typecheck bitslice syntax
    This primarily consists of disambiguating between array indexing and bitslicing
    Note that this function is almost identical to tc_slice_lexpr
 *)
and tc_slice_expr (env: Env.t) (u: unifier) (loc: AST.l) (x: expr) (ss: (AST.slice * AST.ty) list): (AST.expr * AST.ty) =
    if List.length ss == 0 then begin
        raise (TypeError (loc, "empty list of subscripts"))
    end;
    let ss' = List.map fst ss in
    let (x', ty) = tc_expr env u loc x in
    (match derefType (Env.globals env) ty with
    | Type_Array(ixty, elty) ->
            (match ss with
            | [(Slice_Single i, ity)] ->
                    check_type env u loc (ixtype_basetype ixty) ity;
                    (Expr_Array(x', i), elty)
            | _ -> raise (TypeError (loc, "multiple subscripts for array"))
            )
    | Type_Bits(n) ->
            (Expr_Slices(x', ss'), type_bits (slices_width ss'))
    | Type_Register (wd, _) ->
            (Expr_Slices(x', ss'), type_bits (slices_width ss'))
    | Type_Constructor tc when tc = Ident "integer" ->
            (* todo: desugar into a call to slice_int? *)
            (Expr_Slices(x', ss'), type_bits (slices_width ss'))
    | _ -> raise (TypeError (loc, "slice of expr"))
    )

(** Typecheck expression *)
and tc_expr (env: Env.t) (u: unifier) (loc: AST.l) (x: AST.expr): (AST.expr * AST.ty) =
    (match x with
    | Expr_If(c, t, els, e) ->
            let c'        = check_expr env loc type_bool c in
            let (t', tty)     = tc_expr env u loc t in
            let (els', eltys) = List.split (List.map (tc_e_elsif env u loc) els) in
            let (e', ety)     = tc_expr env u loc e in
            List.iter (fun elty -> check_type env u loc tty elty) eltys;
            check_type env u loc tty ety;
            (Expr_If(c', t', els', e'), tty)
    | Expr_Binop(x, Binop_Eq, Expr_LitMask(y)) ->
            (* syntactic sugar *)
            tc_expr env u loc (Expr_In(x, Pat_LitMask y))
    | Expr_Binop(x, Binop_NtEq, Expr_LitMask(y)) ->
            (* syntactic sugar *)
            tc_expr env u loc (Expr_Unop (Unop_BoolNot, (Expr_In(x, Pat_LitMask y))))
    | Expr_Binop(x, op, y) ->
            let (x', xty) = tc_expr env u loc x in
            let (y', yty) = tc_expr env u loc y in
            let (f, tes, ty) = tc_binop (Env.globals env) u loc op x' y' xty yty in
            (Expr_TApply(f, tes, [x'; y']), ty)
    | Expr_Field(e, f) ->
            let (e', ty) = tc_expr env u loc e in
            (match typeFields (Env.globals env) loc ty with
            | FT_Record rfs ->
                (Expr_Field(e', f), get_recordfield loc rfs f)
            | FT_Register rfs ->
                let (ss, ty') = get_regfield loc rfs f in
                (Expr_Slices(e', ss), ty')
            )
    | Expr_Fields(e, fs) ->
            let (e', ty) = tc_expr env u loc e in
            (match typeFields (Env.globals env) loc ty with
            | FT_Record rfs ->
                let tys = List.map (get_recordfield loc rfs) fs in
                (Expr_Fields(e', fs), mk_concat_tys tys)
            | FT_Register rfs ->
                let (ss, ty') = get_regfields loc rfs fs in
                (Expr_Slices(e', ss), ty')
            )
    | Expr_Slices(e, ss) ->
            let all_single = List.for_all (function (Slice_Single _) -> true | _ -> false) ss in
            let ss' = List.map (tc_slice env u loc) ss in

            (* Note that the order of the following check is critical:
             * First check for getter functions then check for arrays or bitvectors because
             * of conflicting names like SPSR and SPSR[] in the v8-A specification.
             *)

            (* variable slice or getter call? *)
            (match e with
            | Expr_Var(a) ->
                let tys = List.map (function (_, ty) -> ty) ss' in
                let getters = GlobalEnv.getFuns (Env.globals env) (addSuffix a "read") in
                let ogetters = chooseFunction (Env.globals env) loc "getter function" (pprint_ident a) true tys getters in
                (match ogetters with
                | Some fty when all_single ->
                    let es = List.map (function (Slice_Single a, _) -> a | _ -> raise (InternalError "Expr_Slices")) ss' in
                    let (f', tes', rty) = instantiate_fun (Env.globals env) u loc fty es tys in
                    (Expr_TApply (f', tes', es), rty)
                | _ ->
                    tc_slice_expr env u loc e ss'
                )
            | _ ->
                tc_slice_expr env u loc e ss'
            )

    | Expr_In(e, p) ->
            let (s, (e', ety')) = with_unify env loc (fun u -> tc_expr env u loc e) in
            let e''   = unify_subst_e  s e' in
            let ety'' = unify_subst_ty s ety' in
            if verbose then Printf.printf "    - Typechecking %s IN ... : %s\n" (pp_expr e') (pp_type ety');
            let p' = tc_pattern env loc ety'' p in
            (Expr_In(e'', p'), type_bool)
    | Expr_Var(v) ->
            (match Env.getVar env v with
            | Some (v', ty') ->
                (Expr_Var(v'),  ty')
            | None ->
                let getters = GlobalEnv.getFuns (Env.globals env) (addSuffix v "read") in
                (match chooseFunction (Env.globals env) loc "getter function" (pprint_ident v) false [] getters with
                | Some fty ->
                    let (f', tes', rty) = instantiate_fun (Env.globals env) u loc fty [] [] in
                    (Expr_TApply (f', tes', []), rty)
                | None -> raise (UnknownObject(loc, "variable or getter functions", pprint_ident v))
                )
            )
    | Expr_Parens(e) ->
            let (e', ty) = tc_expr env u loc e in
            (Expr_Parens(e'), ty)
    | Expr_TApply(f, tes, es) ->
            let (es', tys) = List.split (tc_exprs env u loc es) in
            let (f', tes'', ty) = tc_apply (Env.globals env) u loc "function" f es' tys in
            (Expr_TApply(f', tes'', es'), ty)
    | Expr_Tuple(es) ->
            let (es', tys) = List.split (List.map (tc_expr env u loc) es) in
            (Expr_Tuple(es'), Type_Tuple(tys))
    | Expr_Unop(op, e) ->
            let (e', ety) = tc_expr env u loc e in
            (* Printf.printf "%s: unop %s : %s\n" (pp_loc loc) (pp_expr e) (pp_type ety); *)
            let (f, tes, ty) = tc_unop (Env.globals env) u loc op e ety in
            (Expr_TApply(f, tes, [e']), ty)
    | Expr_Unknown(t) ->
            let ty' = tc_type env loc t in
            (Expr_Unknown(ty'),  ty')
    | Expr_ImpDef(t, os) ->
            let ty' = tc_type env loc t in
            (Expr_ImpDef(ty', os),  ty')
    | Expr_Array(a, e) ->
            let (a', ty) = tc_expr env u loc a in
            (match derefType (Env.globals env) ty with
            | Type_Array(ixty, elty) ->
                    let e' = check_expr env loc (ixtype_basetype ixty) e in
                    (Expr_Array(a', e'), elty)
            | _ -> raise (TypeError (loc, "subscript of non-array"))
            )
    | Expr_LitInt(i) ->
            (Expr_LitInt(i),  type_integer)
    | Expr_LitHex(i) ->
            (Expr_LitHex(i),  type_integer)
    | Expr_LitReal(r) ->
            (Expr_LitReal(r),  type_real)
    | Expr_LitBits(b) ->
            (Expr_LitBits(b),  type_bitsK (string_of_int (masklength b)))
    | Expr_LitMask(b) ->
            (* todo: this case only exists because of the (bad) sugar of
             * writing "x == '0x'" instead of "x IN '0x'"
             *)
            raise (InternalError "tc_expr: litmask")
    | Expr_LitString(s) ->
            (Expr_LitString(s), type_string)
    )


(** Typecheck list of types *)
and tc_types (env: Env.t) (loc: AST.l) (xs: AST.ty list): AST.ty list =
    List.map (tc_type env loc) xs

(** Typecheck type *)
and tc_type (env: Env.t) (loc: AST.l) (x: AST.ty): AST.ty =
    ( match x with
    | Type_Constructor(tc) ->
            if not (GlobalEnv.isType (Env.globals env) tc) then raise (IsNotA (loc, "type constructor", pprint_ident tc));
            (match GlobalEnv.getType (Env.globals env) tc with
            (* todo: instantiate with type parameters? *)
            | Some (Type_Abbreviation ty') -> derefType (Env.globals env) ty'
            | _ -> Type_Constructor(tc)
            )
    | Type_Bits(n) ->
            let n' = check_expr env loc type_integer n in
            Type_Bits(n')
    | Type_App(tc, es) ->
            if not (GlobalEnv.isTycon (Env.globals env) tc) then raise (IsNotA (loc, "type constructor", pprint_ident tc));
            let es' = List.map (check_expr env loc type_integer) es in
            Type_App(tc, es')
    | Type_OfExpr(e) ->
            let (s, (_, ty)) = with_unify env loc (fun u -> tc_expr env u loc e) in
            unify_subst_ty s ty
    | Type_Register(wd, fs) ->
            let fs' = List.map (fun (ss, f) ->
                let (s, ss') = with_unify env loc (fun u -> List.map (fun s -> fst (tc_slice env u loc s)) ss)
                in
                let ss'' = List.map (subst_slice s) ss' in
                (ss'', f)
            ) fs in
            Type_Register (wd, fs')
    | Type_Array(Index_Enum(tc),ety) ->
            if not (GlobalEnv.isEnum (Env.globals env) tc) then raise (IsNotA (loc, "enumeration type", pprint_ident tc));
            let ety' = tc_type env loc ety in
            Type_Array(Index_Enum(tc),ety')
    | Type_Array(Index_Range(lo,hi),ety) ->
            let lo' = check_expr env loc type_integer lo in
            let hi' = check_expr env loc type_integer hi in
            let ety' = tc_type env loc ety in
            Type_Array(Index_Range(lo',hi'),ety')
    | Type_Tuple(tys) ->
            let tys' = tc_types env loc tys in
            Type_Tuple(tys')
    )


(****************************************************************)
(** {2 Typecheck L-expressions}                                 *)
(****************************************************************)

(** Typecheck bitslice syntax

    This primarily consists of disambiguating between array indexing and bitslicing
    Note that this function is almost identical to tc_slice_expr
 *)
let rec tc_slice_lexpr (env: Env.t) (u: unifier) (loc: AST.l) (x: lexpr) (ss: (AST.slice * AST.ty) list): (AST.lexpr * AST.ty) =
    if List.length ss == 0 then begin
        raise (TypeError (loc, "empty list of subscripts"))
    end;
    let ss' = List.map fst ss in
    let (x', ty) = tc_lexpr2 env u loc x in
    (match derefType (Env.globals env) ty with
    | Type_Array(ixty, elty) ->
            (match ss with
            | [(Slice_Single i, ity)] ->
                    check_type env u loc (ixtype_basetype ixty) ity;
                    (LExpr_Array (x', i), elty)
            | _ -> raise (TypeError (loc, "multiple subscripts for array"))
            )
    | Type_Bits(n) ->
            (LExpr_Slices(x', ss'), type_bits (slices_width ss'))
    | Type_Register (wd, _) ->
            (LExpr_Slices(x', ss'), type_bits (slices_width ss'))
    | Type_Constructor tc when tc = Ident "integer" ->
            (* There is an argument for making this operation illegal *)
            printf "Warning: slice assignment of integer at %s\n" (pp_loc loc);
            (LExpr_Slices(x', ss'), type_bits (slices_width ss'))
    | _ -> raise (TypeError (loc, "slice of lexpr"))
    )

(** Typecheck left hand side of expression in context where
    type of right hand side is not yet known
 *)
and tc_lexpr2 (env: Env.t) (u: unifier) (loc: AST.l) (x: AST.lexpr): (AST.lexpr * AST.ty) =
    ( match x with
    | LExpr_Wildcard ->
        raise (TypeError (loc, "wildcard in lexpr2"))
    | LExpr_Var(v) ->
        (match Env.getVar env v with
        | Some (v', ty') ->
            Env.markModified env v;
            (LExpr_Var(v'), ty')
        | None ->
            let getters = GlobalEnv.getFuns (Env.globals env) (addSuffix v "read") in
            let setters = GlobalEnv.getFuns (Env.globals env) (addSuffix v "write") in
            let ogetter = chooseFunction (Env.globals env) loc "var getter function" (pprint_ident v) false [] getters in
            (match ogetter with
            | Some fty ->
                let (_, _, _, _, _, rty) = fty in
                let gty = (match chooseFunction (Env.globals env) loc "var setter function" (pprint_ident v) false [rty] setters with
                | Some gty -> gty
                | None -> raise (UnknownObject(loc, "var setter function", pprint_ident v))
                ) in
                let (f', tes', rty) = instantiate_fun (Env.globals env) u loc fty [] [] in
                (LExpr_ReadWrite (f', ft_id gty, tes', []), rty)
            | None ->
                raise (UnknownObject(loc, "variable", pprint_ident v))
            )
        )
    | LExpr_Field(l, f) ->
        let (l', ty) = tc_lexpr2 env u loc l in
        (match typeFields (Env.globals env) loc ty with
        | FT_Record rfs ->
            (LExpr_Field(l', f), get_recordfield loc rfs f)
        | FT_Register rfs ->
            let (ss, ty') = get_regfield loc rfs f in
            (LExpr_Slices(l', ss), ty')
        )
    | LExpr_Fields(l, fs) ->
        let (l', ty) = tc_lexpr2 env u loc l in
        (match typeFields (Env.globals env) loc ty with
        | FT_Record rfs ->
            let tys = List.map (get_recordfield loc rfs) fs in
            (LExpr_Fields(l', fs), mk_concat_tys tys)
        | FT_Register rfs ->
            let (ss, ty') = get_regfields loc rfs fs in
            (LExpr_Slices(l', ss), ty')
        )
    | LExpr_Slices(e, ss) ->
        let all_single = List.for_all (function (Slice_Single _) -> true | _ -> false) ss in
        let ss' = List.map (tc_slice env u loc) ss in

        (* variable slice or setter call?
         * Start by testing for getter/setter pair
         * If that fails, test for an array variable or bitvector variable
         *)
        (match e with
        | LExpr_Var(a) ->
            let tys = List.map (function (_, ty) -> ty) ss' in
            let getters = GlobalEnv.getFuns (Env.globals env) (addSuffix a "read") in
            let setters = GlobalEnv.getSetterFun (Env.globals env) (addSuffix a "write") in
            let ogetters = chooseFunction (Env.globals env) loc "getter function" (pprint_ident a) true tys getters in
            let osetters = chooseSetterFunction (Env.globals env) loc "setter function" a tys setters in
            (match (ogetters, osetters) with
            | (Some fty, Some gty) when all_single ->
                (* todo: check for Formal_InOut and check that corresponding argument is a legal lexpr *)
                let es = List.map (function (Slice_Single a, _) -> a | _ -> raise (InternalError "Expr_Slices")) ss' in
                let (f', tes', rty) = instantiate_fun (Env.globals env) u loc fty es tys in
                (LExpr_ReadWrite(f', sft_id gty, tes', es), rty)
            | (None,   Some _) -> raise (UnknownObject(loc, "getter function", pprint_ident a))
            | (Some _, None)   -> raise (UnknownObject(loc, "setter function", pprint_ident a))
            | _ -> tc_slice_lexpr env u loc e ss'
            )
        | _ ->
            tc_slice_lexpr env u loc e ss'
        )

    | LExpr_BitTuple(ls) ->
        let (ls', tys) = List.split (List.map (tc_lexpr2 env u loc) ls) in
        let ty = mk_concat_tys tys in
        (LExpr_BitTuple(ls'), ty)
    | LExpr_Tuple(ls) ->
        let (ls', tys) = List.split (List.map (tc_lexpr2 env u loc) ls) in
        (LExpr_Tuple(ls'), Type_Tuple(tys))
    | LExpr_Array(a, e) ->
        let (a', ty) = tc_lexpr2 env u loc a in
        (match derefType (Env.globals env) ty with
        | Type_Array(ixty, elty) ->
                let e' = check_expr env loc (ixtype_basetype ixty) e in
                (LExpr_Array(a', e'), elty)
        | _ -> raise (TypeError (loc, "subscript of non-array"))
        )
    | _ -> raise (InternalError "tc_lexpr2")
    )


(****************************************************************)
(** {2 Typecheck statements}                                    *)
(****************************************************************)

(** Typecheck left hand side of expression and check that rhs type 'ty' is compatible.
    Return set of variables assigned to in this expression
 *)
let rec tc_lexpr (env: Env.t) (u: unifier) (loc: AST.l) (ty: AST.ty) (x: AST.lexpr): (AST.lexpr * implicitVars) =
    ( match x with
    | LExpr_Wildcard ->
        (LExpr_Wildcard, [])
    | LExpr_Var(v) when v == Ident "_" -> (* treat '_' as wildcard token *)
        (LExpr_Wildcard, [])
    | LExpr_Var(v) ->
        (match Env.getVar env v with
        | Some (_, ty') ->
            check_type env u loc ty' ty;
            Env.markModified env v;
            (LExpr_Var v, [])
        | None ->
            let setters = GlobalEnv.getFuns (Env.globals env) (addSuffix v "write") in
            let osetter = chooseFunction (Env.globals env) loc "var setter function" (pprint_ident v) false [ty] setters in
            (match osetter with
            | Some gty ->
                let dummy_arg = Expr_LitInt("42") in (* the value and type of this are ignored *)
                let (g', tes', rty) = instantiate_fun (Env.globals env) u loc gty [dummy_arg] [ty] in
                (LExpr_Write (ft_id gty, tes', []), [])
            | None ->
                (* Implicitly declared variable *)
                Env.markModified env v;
                (LExpr_Var v, [(v, ty)])
            )
        )
    | LExpr_Field(l, f) ->
        let (l', rty) = tc_lexpr2 env u loc l in
        let (r,  ty') = (match typeFields (Env.globals env) loc rty with
            | FT_Record rfs ->
                (LExpr_Field(l', f), get_recordfield loc rfs f)
            | FT_Register rfs ->
                let (ss, ty') = get_regfield loc rfs f in
                (LExpr_Slices(l', ss), ty')
            )
        in
        check_type env u loc ty' ty;
        (r, [])
    | LExpr_Fields(l, fs) ->
        let (l', lty) = tc_lexpr2 env u loc l in
        let (r,  ty') = (match typeFields (Env.globals env) loc lty with
            | FT_Record rfs ->
                let tys = List.map (get_recordfield loc rfs) fs in
                (LExpr_Fields(l', fs), mk_concat_tys tys)
            | FT_Register rfs ->
                let (ss, ty') = get_regfields loc rfs fs in
                (LExpr_Slices(l', ss), ty')
            )
        in
        check_type env u loc ty' ty;
        (r, [])
    | LExpr_Slices(e, ss) ->
        let all_single = List.for_all (function (Slice_Single _) -> true | _ -> false) ss in
        let ss' = List.map (tc_slice env u loc) ss in

        (* variable slice or setter call?
         * Start by testing for getter/setter pair
         * If that fails, test for slice of a var-getter
         * If that fails, test for an array variable or bitvector variable
         *)
        let (e', ty') = (match e with
            | LExpr_Var(a) ->
                let tys = List.map (function (_, ty) -> ty) ss' in
                let setters = GlobalEnv.getSetterFun (Env.globals env) (addSuffix a "write") in
                let osetters = chooseSetterFunction (Env.globals env) loc "setter function" a tys setters in
                (match osetters with
                | Some gty when all_single ->
                    (* todo: check for Formal_InOut and check that corresponding argument is a legal lexpr *)
                    let es = List.map (function (Slice_Single a, _) -> a | _ -> raise (InternalError "Expr_Slices1")) ss' in
                    let (g', tes') = instantiate_sfun (Env.globals env) u loc gty es tys ty in
                    (LExpr_Write(sft_id gty, tes', es), ty)
                | _ ->
                    let getters = GlobalEnv.getFuns (Env.globals env) (addSuffix a "read") in
                    let setters = GlobalEnv.getFuns (Env.globals env) (addSuffix a "write") in
                    let vty = type_bitsK "0" in (* note that width is ignored *)
                    let ogetter = chooseFunction (Env.globals env) loc "var getter function" (pprint_ident a) false [] getters in
                    let osetter = chooseFunction (Env.globals env) loc "var setter function" (pprint_ident a) false [vty] setters in
                    (match (ogetter, osetter) with
                    | (Some fty, Some (g, _, tvs, _, ftys, rty)) ->
                        (* todo: calculate type correctly *)
                        let wr = LExpr_ReadWrite(ft_id fty, g, [], []) in
                        (* todo: check slices are integer *)
                        (* todo: check rty is bits(_) *)
                        let ss'' = List.map fst ss' in
                        (LExpr_Slices(wr, ss''), type_bits (slices_width ss''))
                    | (None,   Some _) -> raise (UnknownObject(loc, "var getter function", pprint_ident a))
                    | (Some _, None)   -> raise (UnknownObject(loc, "var setter function", pprint_ident a))
                    | (None,   None)   -> tc_slice_lexpr env u loc e ss'
                    )
                )
            | _ ->
                tc_slice_lexpr env u loc e ss'
        ) in
        check_type env u loc ty' ty;
        (e', [])

    | LExpr_BitTuple(ls) ->
        let (ls', tys) = List.split (List.map (tc_lexpr2 env u loc) ls) in
        let ty' = mk_concat_tys tys in
        check_type env u loc ty' ty;
        (LExpr_BitTuple(ls'), [])
    | LExpr_Tuple(ls) ->
        let (ls', iss) = (match ty with
            | Type_Tuple tys when List.length ls = List.length tys ->
                List.split (List.map2 (tc_lexpr env u loc) tys ls)
            | _ -> raise (IsNotA(loc, "tuple of length ?", pp_type ty))
        ) in
        (LExpr_Tuple(ls'), List.concat iss)
    | LExpr_Array(a, e) ->
        let (a', ty) = tc_lexpr2 env u loc a in
        (match derefType (Env.globals env) ty with
        | Type_Array(ixty, elty) ->
                let (e', ety) = tc_expr env u loc e in
                check_type env u loc (ixtype_basetype ixty) ety;
                (LExpr_Array(a', e'), [])
        | _ -> raise (TypeError (loc, "subscript of non-array"))
        )
    | _ -> raise (InternalError "tc_lexpr")
    )

(** Typecheck list of statements *)
let rec tc_stmts (env: Env.t) (loc: AST.l) (xs: AST.stmt list): AST.stmt list =
    let rss = Env.nest (fun env' -> List.map (fun s ->
        let s' = tc_stmt env' s in
        let imps = Env.getImplicits env' in
        List.iter (fun (v, ty) -> Env.addLocalVar env' loc v ty) imps;
        let decls = declare_implicits loc imps in
        if verbose && decls <> [] then Printf.printf "Implicit decls: %s %s" (pp_loc loc) (Utils.to_string (PP.pp_indented_block decls));
        List.append decls [s']
    ) xs
    ) env in
    List.concat rss

(** Typecheck 'if expr then stmt' *)
and tc_s_elsif (env: Env.t) (loc: AST.l) (x: AST.s_elsif): AST.s_elsif =
    (match x with
    | S_Elsif_Cond(c, s) ->
            let c' = check_expr env loc type_bool c in
            let s' = tc_stmts env loc s in
            S_Elsif_Cond(c', s')
    )

(** Typecheck case alternative *)
and tc_alt (env: Env.t) (loc: AST.l) (ty: AST.ty) (x: AST.alt): AST.alt =
    (match x with
    | Alt_Alt(ps, oc, b) ->
            let ps' = List.map (tc_pattern env loc ty) ps in
            let oc' = map_option (fun c -> check_expr env loc type_bool c) oc in
            let b' = tc_stmts env loc b in
            Alt_Alt(ps', oc', b')
    )

(** Typecheck exception catcher 'when expr stmt' *)
and tc_catcher (env: Env.t) (loc: AST.l) (x: AST.catcher): AST.catcher =
    (match x with
    | Catcher_Guarded(c, b) ->
            let c' = check_expr env loc type_bool c in
            let b' = tc_stmts env loc b in
            Catcher_Guarded(c', b')
    )

(** Typecheck statement *)
and tc_stmt (env: Env.t) (x: AST.stmt): AST.stmt =
    (match x with
    | Stmt_VarDeclsNoInit(ty, vs, loc) ->
            let ty' = tc_type env loc ty in
            List.iter (fun v -> Env.addLocalVar env loc v ty') vs;
            Stmt_VarDeclsNoInit(ty', vs, loc)
    | Stmt_VarDecl(ty, v, i, loc) ->
            let ty' = tc_type env loc ty in
            let i' = check_expr env loc ty' i in
            Env.addLocalVar env loc v ty';
            Stmt_VarDecl(ty', v, i', loc)
    | Stmt_ConstDecl(ty, v, i, loc) ->
            let ty' = tc_type env loc ty in
            let i'  = check_expr env loc ty' i in
            Env.addLocalVar env loc v ty';
            if ty' = type_integer then Env.addConstraint env loc (mk_eq_int (Expr_Var v) i');
            Stmt_ConstDecl(ty', v, i', loc)
    | Stmt_Assign(l, r, loc) ->
            let (s, (r', rty, l', imps)) = with_unify env loc (fun u ->
                let (r', rty)  = tc_expr env u loc r in
                let (l', imps) = tc_lexpr env u loc rty l in
                if verbose then Printf.printf "    - Typechecking %s <- %s : %s\n" (pp_lexpr l') (pp_expr r') (pp_type rty);
                (r', rty, l', imps)
            ) in
            let l'' = unify_subst_le s l' in
            let r'' = unify_subst_e  s r' in
            List.iter (fun (v, ty) ->
                let ty' = unify_subst_ty s ty in
                (* todo: note that type potentially involves local variables
                 * eg in assignments like "x = address[31:N] : Zeros(N);"
                 * whose "obvious" type is "bits(((31-N)+1)+N)"
                 *
                 * We could attempt to simplify the type (in this example,
                 * it could be simplified to "bits(32)"), this would be somewhat
                 * fragile (unless we can guarantee that the simplified expression
                 * does not involve any variables that it does not need to involve).
                 *
                 * So, we do not simplify the expression and, instead, we
                 * declare the variable in the outermost scope in which all
                 * free variables are in scope.
                 *
                 * (That said, it may be a worthwhile optimization to simplify
                 * the expression before execution to avoid gratuitiously complex
                 * bitwidth calculations.)
                 *)
                Env.addLocalImplicitVar env loc v ty'
            ) imps;
            Stmt_Assign(l'', r'', loc)
    | Stmt_TCall(f, tes, es, loc) ->
            let (s, (f', tes'', es')) = with_unify env loc (fun u ->
                let (es', tys) = List.split (tc_exprs env u loc es) in
                let (f', tes'', ty) = tc_apply (Env.globals env) u loc "procedure" f es' tys in
                check_type env u loc ty type_unit;
                (f', tes'', es')
            ) in
            let es''   = List.map (unify_subst_e s) es' in
            let tes''' = List.map (unify_subst_e s) tes'' in
            Stmt_TCall(f', tes''', es'', loc)
    | Stmt_FunReturn(e, loc) ->
            let rty = (match Env.getReturnType env with
            | Some ty -> ty
            | None    -> raise (InternalError "Stmt_FunReturn")
            ) in
            let e' = check_expr env loc rty e in
            Stmt_FunReturn(e', loc)
    | Stmt_ProcReturn(loc) ->
            (match Env.getReturnType env with
            | None -> ()
            | Some (Type_Tuple []) -> ()
            | _ -> raise (InternalError "return type should be None")
            );
            Stmt_ProcReturn(loc)
    | Stmt_Assert(e, loc) ->
            let e' = check_expr env loc type_bool e in
            Stmt_Assert(e', loc)
    | Stmt_Unpred(loc) ->
            Stmt_Unpred(loc)
    | Stmt_ConstrainedUnpred(loc) ->
            Stmt_ConstrainedUnpred(loc)
    | Stmt_ImpDef(s, loc) ->
            Stmt_ImpDef(s, loc)
    | Stmt_Undefined(loc) ->
            Stmt_Undefined(loc)
    | Stmt_ExceptionTaken(loc) ->
            Stmt_ExceptionTaken(loc)
    | Stmt_Dep_Unpred(loc) ->
            Stmt_Dep_Unpred(loc)
    | Stmt_Dep_ImpDef(s, loc) ->
            Stmt_Dep_ImpDef(s, loc)
    | Stmt_Dep_Undefined(loc) ->
            Stmt_Dep_Undefined(loc)
    | Stmt_See(e, loc) ->
            Stmt_See(e, loc)
    | Stmt_Throw(v, loc) ->
            let _ = with_unify env loc (fun u ->
                let (v', ty) = check_var env loc v in
                check_type env u loc type_exn ty
            ) in
            Stmt_Throw(v, loc)
    | Stmt_If(c, t, els, e, loc) ->
            let c'   = check_expr env loc type_bool c in
            let t'   = tc_stmts env loc t in
            let els' = List.map (tc_s_elsif env loc) els in
            let e'   = tc_stmts env loc e in
            Stmt_If(c', t', els', e', loc)
    | Stmt_Case(e, alts, odefault, loc) ->
            let (s, (e', ty')) = with_unify env loc (fun u -> tc_expr env u loc e) in
            let e''       = unify_subst_e  s e' in
            let ty''      = unify_subst_ty s ty' in
            let alts'     = List.map (tc_alt env loc ty'') alts in
            let odefault' = map_option (fun b -> tc_stmts env loc b) odefault in
            Stmt_Case(e'', alts', odefault', loc)
    | Stmt_For(v, start, dir, stop, b, loc) ->
            let start' = check_expr env loc type_integer start in
            let stop'  = check_expr env loc type_integer stop in
            let b' = Env.nest (fun env' ->
                Env.addLocalVar env' loc v type_integer;
                tc_stmts env' loc b
            ) env in
            let b'' = List.append (declare_implicits loc (Env.getImplicits env)) b' in
            Stmt_For(v, start', dir, stop', b'', loc)
    | Stmt_While(c, b, loc) ->
            let c' = check_expr env loc type_bool c in
            let b' = tc_stmts env loc b in
            Stmt_While(c', b', loc)
    | Stmt_Repeat(b, c, loc) ->
            let b' = tc_stmts env loc b in
            let c' = check_expr env loc type_bool c in
            Stmt_Repeat(b', c', loc)
    | Stmt_Try(tb, ev, catchers, odefault, loc) ->
            let tb' = tc_stmts env loc tb in
            Env.nest (fun env' ->
                Env.addLocalVar env' loc ev type_exn;
                let catchers' = List.map (tc_catcher env' loc) catchers in
                let odefault' = map_option (fun b -> tc_stmts env loc b) odefault in
                Stmt_Try(tb', ev, catchers', odefault', loc)
            ) env
    )


(****************************************************************)
(** {2 Typecheck function definition}                           *)
(****************************************************************)

(** Typecheck function body (list of statements) *)
let tc_body (env: Env.t) (loc: AST.l) (xs: AST.stmt list): AST.stmt list =
    let xs' = tc_stmts env loc xs in
    let imps = Env.getAllImplicits env in
    let decls = declare_implicits loc imps in
    if verbose && decls <> [] then Printf.printf "Implicit decls: %s %s" (pp_loc loc) (Utils.to_string (PP.pp_indented_block decls));
    List.append decls xs'

(** Typecheck function argument *)
let tc_argument (env: Env.t) (loc: AST.l) ((ty, arg): (AST.ty * AST.ident)): (AST.ty * AST.ident) =
    let ty' = tc_type env loc ty in
    Env.addLocalVar env loc arg ty';
    (ty', arg)

(** Typecheck list of function arguments *)
let tc_arguments (env: Env.t) (loc: AST.l) (xs: (AST.ty * AST.ident) list): (AST.ty * AST.ident) list =
    List.map (tc_argument env loc) xs

(** Typecheck setter procedure argument *)
let tc_sformal (env: Env.t) (loc: AST.l) (x: sformal): sformal =
    ( match x with
    | Formal_In(ty,v) ->
            let ty' = tc_type env loc ty in
            Env.addLocalVar env loc v ty';
            Formal_In(ty', v)
    | Formal_InOut(ty,v) ->
            let ty' = tc_type env loc ty in
            Env.addLocalVar env loc v ty';
            Formal_InOut(ty', v)
    )

(** Typecheck list of setter procedure arguments *)
let tc_sformals (env: Env.t) (loc: AST.l) (xs: sformal list): sformal list =
    List.map (tc_sformal env loc) xs

(** Add function definition to environment *)
let addFunction (env: GlobalEnv.t) (loc: AST.l) (qid: AST.ident) (isArr: bool) (tvs: IdentSet.t) (args: (AST.ty * AST.ident) list) (rty: AST.ty): funtype =
    let argtys   = List.map (fun (ty, _) -> ty) args in
    let funs     = GlobalEnv.getFuns env qid in
    let num_funs = List.length funs in
    (match List.filter (isCompatibleFunction env isArr argtys) funs with
    | [] -> (* not defined yet *)
        (* ASL allows multiple functions to share the same name.
         * The typechecker disambiguates functions for the benefit of other parts of the
         * system by adding a unique tag to each ident.
         * We use the number of functions that already have that name as the tag.
         *)
        let tag  = num_funs in
        let qid' = addTag qid tag in
        let fty: funtype = (qid', isArr, IdentSet.elements tvs, [], args, rty) in
        GlobalEnv.addFuns env loc qid (fty :: funs);
        fty
    | [fty] -> (* already defined *)
        fty
    | ftys -> (* internal error: multiple definitions *)
        failwith "addFunction"
    )

let addSetterFunction (env: GlobalEnv.t) (loc: AST.l) (qid: AST.ident) (tvs: IdentSet.t) (args: AST.sformal list) (vty: AST.ty): sfuntype =
    let argtys   = List.map sformal_type args in
    let funs     = GlobalEnv.getSetterFun env qid in
    let num_funs = List.length funs in
    (match List.filter (isCompatibleSetterFunction env argtys) funs with
    | [] -> (* not defined yet *)
        (* ASL allows multiple functions to share the same name.
         * The typechecker disambiguates functions for the benefit of other parts of the
         * system by adding a unique tag to each ident.
         * We use the number of functions that already have that name as the tag.
         *)
        let tag  = num_funs in
        let qid' = addTag qid tag in
        let fty: sfuntype = (qid', IdentSet.elements tvs, [], args, vty) in
        GlobalEnv.addSetterFuns env qid (fty :: funs);
        fty
    | [fty] -> (* already defined *)
        fty
    | ftys -> (* internal error: multiple definitions *)
        failwith "addFunction"
    )


(****************************************************************)
(** {2 Typecheck instruction}                                   *)
(****************************************************************)

(** Typecheck instruction encoding *)
let tc_encoding (env: Env.t) (x: encoding): (encoding * ((AST.ident * AST.ty) list)) =
    (match x with
    | Encoding_Block (nm, iset, fields, opcode, guard, unpreds, b, loc) ->
        GlobalEnv.addEncoding (Env.globals env) nm;
        List.iter (fun (IField_Field (fnm, lo, wd)) ->
            Env.addLocalVar env loc fnm (type_bits (Expr_LitInt (string_of_int wd)))
        ) fields;
        let guard' = check_expr env loc type_bool guard in
        let (b', bs) = Env.nest_with_bindings (fun env' ->
            let b' = tc_stmts env' loc b in
            let imps = Env.getAllImplicits env in
            List.iter (fun (v, ty) -> Env.addLocalVar env' loc v ty) imps;
            let decls = declare_implicits loc imps in
            if verbose && decls <> [] then Printf.printf "Implicit decls: %s %s" (pp_loc loc) (Utils.to_string (PP.pp_indented_block decls));
            List.append decls b'
        ) env in
        (Encoding_Block (nm, iset, fields, opcode, guard', unpreds, b', loc), bs)
    )

(** Typecheck bitslice of instruction opcode *)
let tc_decode_slice (env: int Bindings.t) (loc: AST.l) (x: AST.decode_slice): (AST.decode_slice * int) =
    (match x with
    | DecoderSlice_Slice (lo, wd) -> (DecoderSlice_Slice(lo, wd), wd)
    | DecoderSlice_FieldName f ->
        let wd = (match Bindings.find_opt f env with
        | Some wd -> wd
        | None -> raise (UnknownObject (loc, "instruction field", pprint_ident f))
        ) in
        (DecoderSlice_FieldName f, wd)
    | DecoderSlice_Concat fs ->
        let wds = List.map (fun f -> Bindings.find f env) fs in
        let sum xs = List.fold_left (fun a b -> a + b) 0 xs in
        (DecoderSlice_Concat fs, sum wds)
    )

let check_width (loc: AST.l) (wd1: int) (wd2: int): unit =
    if wd1 != wd2 then
        raise (DoesNotMatch(loc, "width of field", string_of_int wd1, string_of_int wd2))

(** Typecheck instruction decode pattern match *)
let rec tc_decode_pattern (loc: AST.l) (wd: int) (x: decode_pattern): decode_pattern =
    (match x with
    | DecoderPattern_Bits b -> check_width loc wd (masklength b); x
    | DecoderPattern_Mask m -> check_width loc wd (masklength m); x
    | DecoderPattern_Wildcard _ -> x
    | DecoderPattern_Not p ->
            let p' = tc_decode_pattern loc wd p in
            DecoderPattern_Not p'
    )

(** Typecheck instruction decode body *)
let rec tc_decode_body (env: GlobalEnv.t) (x: decode_body): decode_body =
    (match x with
    | DecoderBody_UNPRED _ -> x
    | DecoderBody_UNALLOC _ -> x
    | DecoderBody_NOP _ -> x
    | DecoderBody_Encoding (enc, loc) ->
            if not (GlobalEnv.isEncoding env enc) then
                raise (UnknownObject(loc, "encoding", pprint_ident enc));
            x
    | DecoderBody_Decoder (fs, case, loc) ->
            let case'= tc_decode_case env loc fs case in
            DecoderBody_Decoder (fs, case', loc)
    )

(** Typecheck instruction decode case alternative *)
and tc_decode_alt (env: GlobalEnv.t) (loc: AST.l) (wds: int list) (x: decode_alt): decode_alt =
    (match x with
    | DecoderAlt_Alt (pats, body) ->
        let pats' = List.map2 (tc_decode_pattern loc) wds pats in
        let body' = tc_decode_body env body in
        DecoderAlt_Alt (pats', body')
    )

(** Typecheck instruction decode case *)
and tc_decode_case (env: GlobalEnv.t) (floc: AST.l) (fs: instr_field list) (x: decode_case): decode_case =
    (match x with
    | DecoderCase_Case (slices, alts, loc) ->
        let fenv = List.fold_left (fun r (IField_Field (fnm, lo, wd)) ->
            Bindings.add fnm wd r) Bindings.empty fs
        in
        let (slices', wds) = List.split (List.map (tc_decode_slice fenv loc) slices) in
        let alts' = List.map (tc_decode_alt env loc wds) alts in
        DecoderCase_Case (slices', alts', loc)
    )

(****************************************************************)
(** {2 Typecheck global declaration}                            *)
(****************************************************************)

(** Typecheck global declaration, extending environment as needed *)
let tc_declaration (env: GlobalEnv.t) (d: AST.declaration): AST.declaration list =
    ( match d with
    | Decl_BuiltinType(qid, loc) ->
            GlobalEnv.addType env loc qid (Type_Builtin(qid));
            [d]
    | Decl_Forward(qid, loc) ->
            GlobalEnv.addType env loc qid Type_Forward;
            [d]
    | Decl_Record(qid, fs, loc) ->
            let env' = Env.mkEnv env in
            let fs' = List.map (fun (ty, f) ->
                (tc_type env' loc ty, f)
            ) fs
            in
            GlobalEnv.addType env loc qid (Type_Record(fs'));
            [Decl_Record(qid, fs', loc)]
    | Decl_Typedef(qid, ty, loc) ->
            let ty' = tc_type (Env.mkEnv env) loc ty in
            GlobalEnv.addType env loc qid (Type_Abbreviation(ty'));
            [Decl_Typedef(qid, ty', loc)]
    | Decl_Enum(qid, es, loc) ->
            GlobalEnv.addType env loc qid (Type_Enumeration(es));
            List.iter (fun e -> GlobalEnv.addGlobalVar env loc e (Type_Constructor(qid)) true) es;
            let ty = Type_Constructor(qid) in
            let cmp_args = [(ty, Ident "x"); (ty, Ident "y")] in
            let eq = addFunction env loc (Ident "eq_enum") false IdentSet.empty cmp_args type_bool in
            let ne = addFunction env loc (Ident "ne_enum") false IdentSet.empty cmp_args type_bool in
            GlobalEnv.addOperators2 env loc Binop_Eq   [eq];
            GlobalEnv.addOperators2 env loc Binop_NtEq [ne];
            let deq = Decl_BuiltinFunction(ty, ft_id eq, [], loc) in
            let dne = Decl_BuiltinFunction(ty, ft_id ne, [], loc) in
            [d; deq; dne]
    | Decl_Var(ty, qid, loc) ->
            let ty' = tc_type (Env.mkEnv env) loc ty in
            GlobalEnv.addGlobalVar env loc qid ty' false;
            [Decl_Var(ty', qid, loc)]
    | Decl_Const(ty, qid, i, loc) ->
            let ty' = tc_type (Env.mkEnv env) loc ty in
            let i'  = check_expr (Env.mkEnv env) loc ty' i in
            GlobalEnv.addGlobalVar env loc qid ty' true;
            [Decl_Const(ty', qid, i', loc)]
    | Decl_BuiltinFunction(rty, qid, atys, loc) ->
            let locals = Env.mkEnv env in
            let tvs = fv_funtype (qid, false, [], [], atys, rty) in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let rty'  = tc_type locals loc rty in
            let atys' = tc_arguments locals loc atys in
            let qid'  = ft_id (addFunction env loc qid false tvs atys' rty') in
            [Decl_BuiltinFunction(rty', qid', atys', loc)]
    | Decl_FunType(rty, qid, atys, loc) ->
            let locals = Env.mkEnv env in
            let tvs = fv_funtype (qid, false, [], [], atys, rty) in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let rty'  = tc_type      locals loc rty in
            let atys' = tc_arguments locals loc atys in
            let qid'  = ft_id (addFunction env loc qid false tvs atys' rty') in
            [Decl_FunType(rty', qid', atys', loc)]
    | Decl_FunDefn(rty, qid, atys, b, loc) ->
            let locals = Env.mkEnv env in
            let tvs = fv_funtype (qid, false, [], [], atys, rty) in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let rty'  = tc_type      locals loc rty in
            let atys' = tc_arguments locals loc atys in
            Env.setReturnType locals rty';
            let b'    = tc_body locals loc b in
            let qid'  = ft_id (addFunction env loc qid false tvs atys' rty') in
            [Decl_FunDefn(rty', qid', atys', b', loc)]
    | Decl_ProcType(qid, atys, loc) ->
            let locals = Env.mkEnv env in
            let tvs = fv_args atys in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let atys' = tc_arguments locals loc atys in
            let qid'  = ft_id (addFunction env loc qid false tvs atys' type_unit) in
            [Decl_ProcType(qid', atys', loc)]
    | Decl_ProcDefn(qid, atys, b, loc) ->
            let locals = Env.mkEnv env in
            let tvs = fv_args atys in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let atys' = tc_arguments locals loc atys in
            let b'    = tc_body locals loc b in
            let qid'  = ft_id (addFunction env loc qid false tvs atys' type_unit) in
            [Decl_ProcDefn(qid', atys', b', loc)]
    | Decl_VarGetterType(rty, qid, loc) ->
            let locals = Env.mkEnv env in
            let tvs = fv_type rty in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let rty' = tc_type locals loc rty in
            (* todo: check that if a setter function exists, it has a compatible type *)
            let qid' = ft_id (addFunction env loc (addSuffix qid "read") false tvs [] rty') in
            [Decl_VarGetterType(rty', qid', loc)]
    | Decl_VarGetterDefn(rty, qid, b, loc) ->
            let locals = Env.mkEnv env in
            let tvs = fv_type rty in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let rty' = tc_type locals loc rty in
            (* todo: check that if a setter function exists, it has a compatible type *)
            let qid' = ft_id (addFunction env loc (addSuffix qid "read") false tvs [] rty') in
            Env.setReturnType locals rty';
            let b' = tc_body locals loc b in
            [Decl_VarGetterDefn(rty', qid', b', loc)]
    | Decl_ArrayGetterType(rty, qid, atys, loc) ->
            let locals = Env.mkEnv env in
            let tvs = fv_funtype (qid, false, [], [], atys, rty) in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let rty'  = tc_type      locals loc rty in
            let atys' = tc_arguments locals loc atys in
            let qid'  = ft_id (addFunction env loc (addSuffix qid "read") true tvs atys' rty') in
            (* todo: check that if a setter function exists, it has a compatible type *)
            [Decl_ArrayGetterType(rty', qid', atys', loc)]
    | Decl_ArrayGetterDefn(rty, qid, atys, b, loc) ->
            let locals = Env.mkEnv env in
            let tvs = fv_funtype (qid, false, [], [], atys, rty) in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let rty'  = tc_type      locals loc rty in
            let atys' = tc_arguments locals loc atys in
            (* todo: check that if a setter function exists, it has a compatible type *)
            Env.setReturnType locals rty';
            let qid'  = ft_id (addFunction env loc (addSuffix qid "read") true tvs atys' rty') in
            let b' = tc_body locals loc b in
            [Decl_ArrayGetterDefn(rty', qid', atys', b', loc)]
    | Decl_VarSetterType(qid, ty, v, loc) ->
            let locals = Env.mkEnv env in
            let tvs = fv_type ty in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let ty'   = tc_type locals loc ty in
            Env.addLocalVar locals loc v ty';
            (* todo: check that if a getter function exists, it has a compatible type *)
            (* todo: this obscures the difference between "PC[]" and "PC" *)
            let qid' = ft_id (addFunction env loc (addSuffix qid "write") false tvs [(ty', v)] type_unit) in
            [Decl_VarSetterType(qid', ty', v, loc)]
    | Decl_VarSetterDefn(qid, ty, v, b, loc) ->
            let locals = Env.mkEnv env in
            let tvs = fv_type ty in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let ty'   = tc_type locals loc ty in
            Env.addLocalVar locals loc v ty';
            (* todo: check that if a getter function exists, it has a compatible type *)
            (* todo: this obscures the difference between "PC[]" and "PC" *)
            let qid'  = ft_id (addFunction env loc (addSuffix qid "write") false tvs [(ty', v)] type_unit) in
            let b' = tc_body locals loc b in
            [Decl_VarSetterDefn(qid', ty', v, b', loc)]
    | Decl_ArraySetterType(qid, atys, ty, v, loc) ->
            let locals = Env.mkEnv env in
            let tvs = IdentSet.union (fv_sformals atys) (fv_type ty) in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let atys' = tc_sformals locals loc atys in
            let ty'   = tc_type     locals loc ty in
            Env.addLocalVar locals loc v ty';
            (* todo: check that if a getter function exists, it has a compatible type *)
            let qid' = addSetterFunction env loc (addSuffix qid "write") tvs atys' ty' in
            [Decl_ArraySetterType(sft_id qid', atys', ty', v, loc)]
    | Decl_ArraySetterDefn(qid, atys, ty, v, b, loc) ->
            let locals = Env.mkEnv env in
            let tvs = IdentSet.union (fv_sformals atys) (fv_type ty) in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let atys' = tc_sformals locals loc atys in
            let ty'   = tc_type     locals loc ty in
            (* todo: should I use name mangling or define an enumeration to select
             * which namespace to do lookup in?
             *)
            (* todo: check that if a getter function exists, it has a compatible type *)
            let qid' = addSetterFunction env loc (addSuffix qid "write") tvs atys' ty' in
            Env.addLocalVar locals loc v ty';
            let b' = tc_body locals loc b in
            [Decl_ArraySetterDefn(sft_id qid', atys', ty', v, b', loc)]
    | Decl_InstructionDefn(nm, encs, opost, conditional, exec, loc) ->
            let locals = Env.mkEnv env in
            let (encs', vss) = List.split (List.map (tc_encoding locals) encs) in

            (* todo: check consistency of bindings from different encodings *)
            (* todo: ponder what to do when encodings don't all define the same variables *)
            List.iter (fun vs -> List.iter (fun (v, ty) -> Env.addLocalVar locals loc v ty) vs) vss;

            let opost' = map_option (tc_stmts locals loc) opost in
            let exec' = tc_stmts locals loc exec in
            [Decl_InstructionDefn(nm, encs', opost', conditional, exec', loc)]
    | Decl_DecoderDefn(nm, case, loc) ->
            let case' = tc_decode_case env loc [] case in
            [Decl_DecoderDefn(nm, case', loc)]
    | Decl_Operator1(op, funs, loc) ->
            let funs' = List.concat (List.map (fun f ->
                let fs = GlobalEnv.getFuns env f in
                if fs = [] then raise (UnknownObject(loc, "unary operator implementation", pprint_ident f));
                fs
            ) funs) in
            GlobalEnv.addOperators1 env loc op funs';
            [Decl_Operator1(op, List.map ft_id funs', loc)]
    | Decl_Operator2(op, funs, loc) ->
            let funs' = List.concat (List.map (fun f ->
                let fs = GlobalEnv.getFuns env f in
                if fs = [] then raise (UnknownObject(loc, "binary operator implementation", pprint_ident f));
                fs
            ) funs) in
            GlobalEnv.addOperators2 env loc op funs';
            [Decl_Operator2(op, List.map ft_id funs', loc)]
    | Decl_NewEventDefn(qid, atys, loc) -> (* very similar to Decl_ProcType *)
            let locals = Env.mkEnv env in
            let tvs = fv_args atys in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let atys' = tc_arguments locals loc atys in
            let qid'  = ft_id (addFunction env loc qid false tvs atys' type_unit) in
            [Decl_NewEventDefn(qid', atys', loc)]
    | Decl_EventClause(nm, b, loc) ->
            let locals = Env.mkEnv env in
            (match GlobalEnv.getFuns env nm with
            | [r] ->
                (* todo: put event args in scope *)
                let b' = tc_body locals loc b in
                [Decl_EventClause(ft_id r, b', loc)]
            | [] ->
                raise (UnknownObject(loc, "event", pprint_ident nm))
            | fs  ->
                reportChoices loc "event" (pprint_ident nm) [] fs;
                raise (Ambiguous (loc, "event", pprint_ident nm))
            )
    | Decl_NewMapDefn(rty, qid, atys, b, loc) -> (* very similar to Decl_FunDefn *)
            let locals = Env.mkEnv env in
            let tvs = fv_funtype (qid, false, [], [], atys, rty) in
            IdentSet.iter (fun tv -> Env.addLocalVar locals loc tv type_integer) tvs;
            let rty'  = tc_type      locals loc rty in
            Env.setReturnType locals rty';
            let atys' = tc_arguments locals loc atys in
            let qid'  = ft_id (addFunction env loc qid false tvs atys' rty') in
            let b'    = tc_body locals loc b in
            [Decl_NewMapDefn(rty', qid', atys', b', loc)]
    | Decl_MapClause(nm, fs, oc, b, loc) ->
            (* todo: check fs, oc and body *)
            [Decl_MapClause(nm, fs, oc, b, loc)]
    | Decl_Config(ty, qid, i, loc) -> (* very similar to Decl_Const *)
            let locals = Env.mkEnv env in
            let ty' = tc_type locals loc ty in
            let i'  = check_expr locals loc ty' i in
            GlobalEnv.addGlobalVar env loc qid ty true;
            [Decl_Config(ty', qid, i', loc)]
    )

(** Generate function prototype declarations.

    This allows function declarations within a translation unit to be
    placed in any order.
 *)
let genPrototypes (ds: AST.declaration list): (AST.declaration list * AST.declaration list) =
    let pre : (AST.declaration list) ref = ref [] in
    let post : (AST.declaration list) ref = ref [] in
    List.iter (fun d ->
        (match d with
        | Decl_FunDefn(rty, qid, atys, _, loc) ->
                post := d :: !post;
                pre := Decl_FunType(rty, qid, atys, loc) :: !pre
        | Decl_ProcDefn(qid, atys, _, loc) ->
                post := d :: !post;
                pre := Decl_ProcType(qid, atys, loc) :: !pre
        | Decl_VarGetterDefn(rty, qid, _, loc) ->
                post := d :: !post;
                pre := Decl_VarGetterType(rty, qid, loc) :: !pre
        | Decl_ArrayGetterDefn(rty, qid, atys, _, loc) ->
                post := d :: !post;
                pre := Decl_ArrayGetterType(rty, qid, atys, loc) :: !pre
        | Decl_VarSetterDefn(qid, ty, v, _, loc) ->
                post := d :: !post;
                pre := Decl_VarSetterType(qid, ty, v, loc) :: !pre
        | Decl_ArraySetterDefn(qid, atys, ty, v, _, loc) ->
                post := d :: !post;
                pre := Decl_ArraySetterType(qid, atys, ty, v, loc) :: !pre
        | Decl_NewEventDefn(qid, atys, loc) ->
                post := d :: !post;
                (* todo: replacing it with a function declaration is not
                 * completely kosher *)
                pre := Decl_ProcType(qid, atys, loc) :: !pre
        | Decl_NewMapDefn(rty, qid, atys, b, loc) ->
                post := d :: !post;
                (* todo: replacing it with a function declaration is not
                 * completely kosher *)
                pre := Decl_FunType(rty, qid, atys, loc) :: !pre
        | Decl_EventClause(nm, b, loc) ->
                post := d :: !post;
        | Decl_MapClause(nm, fs, oc, b, loc) ->
                post := d :: !post;
        | _ ->
                pre := d :: !pre
        )
    ) ds;
    (List.rev !pre, List.rev !post)

(** Overall typechecking environment shared by all invocations of typechecker *)
let env0 = GlobalEnv.mkempty ()

(** Typecheck a list of declarations - main entrypoint into typechecker *)
let tc_declarations (isPrelude: bool) (ds: AST.declaration list): AST.declaration list =
    if verbose then Printf.printf "  - Using Z3 %s\n" Z3.Version.to_string;
    (* Process declarations, starting by moving all function definitions to the
     * end of the list and replacing them with function prototypes.
     * As long as the type/var decls are all sorted correctly, this
     * is enough to handle functions that are used before being defined.
     *
     * Note that each declaration is evaluated in a separate local environment
     * but that they share the same global environment
     *)
    let (pre, post) = if isPrelude then (ds, []) else genPrototypes ds in
    if verbose then Printf.printf "  - Typechecking %d phase 1 declarations\n" (List.length pre);
    let pre'  = List.map (tc_declaration env0) pre  in
    let post' = List.map (tc_declaration env0) post in
    if verbose then List.iter (fun ds -> List.iter (fun d -> Printf.printf "\nTypechecked %s\n" (Utils.to_string (PP.pp_declaration d))) ds) post';
    if verbose then Printf.printf "  - Typechecking %d phase 2 declarations\n" (List.length post);
    List.append (List.concat pre') (List.concat post')

(****************************************************************
 * End
 ****************************************************************)
