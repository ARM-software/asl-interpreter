(****************************************************************
 * ASL utility functions
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** ASL utility functions *)

module PP   = Asl_parser_pp
module AST  = Asl_ast
module Visitor = Asl_visitor

open AST
open Visitor

(****************************************************************)
(** {2 Bindings and IdentSet}                                   *)
(****************************************************************)

(** {2 Bindings: maps indexed by identifiers} *)
module Bindings = Map.Make(AST.Id)

(** add association list to bindings *)
let add_bindings (bs: 'a Bindings.t) (xs: (ident * 'a) list): 'a Bindings.t =
    List.fold_left (fun a (k, v) -> Bindings.add k v a) bs xs

(** create bindings from association list *)
let mk_bindings (xs: (ident * 'a) list): 'a Bindings.t =
    add_bindings Bindings.empty xs

(** print bindings *)
let pp_bindings (pp: 'a -> string) (bs: 'a Bindings.t): string =
    String.concat ", " (List.map (fun (k, v) -> pprint_ident k ^"->"^ pp v) (Bindings.bindings bs))


(** {2 Sets of identifiers} *)
module IdentSet = Set.Make(Id)

(** merge a list of sets *)
let unionSets (idss: IdentSet.t list): IdentSet.t =
    List.fold_left IdentSet.union IdentSet.empty idss

(** add v to set of identifiers mapped to k *)
let addToBindingSet (k: ident) (v: ident) (bs: IdentSet.t Bindings.t): IdentSet.t Bindings.t =
    Bindings.update k (fun old ->
        (match old with
        | None    -> Some (IdentSet.singleton v)
        | Some vs -> Some (IdentSet.add v vs)
        )
    ) bs

(** convert identifier set to sorted list of identifiers

    The implementation is trivial and exists mostly to emphasize that the
    resulting list is sorted
 *)
let to_sorted_list (s: IdentSet.t): ident list =
    IdentSet.elements s


(****************************************************************)
(** {2 Equivalence classes}                                     *)
(****************************************************************)

(** Equivalence classes are represented by trees.

    The root of the tree is the canonical member of the class.
    Traversing the parent node takes you closer to the canonical member.
    The root is its own parent.
 *)
type tree = {
    mutable parent : tree;
    data : ident;
}

(** Equivalence class support (to support unification, and similar)

    The implementation is based on
    {{:https://en.wikipedia.org/wiki/Disjoint-set_data_structure}Wikipedia: Union-Find}.
    I have not implemented all the optimizations they suggest
    because I expect sets to be quite small in practice.
 *)

class equivalences = object (self)

    (* Mapping from elements to the set containing them *)
    val mutable forest : tree Bindings.t = Bindings.empty

    (* Find the root (canonical member of) the set.
     * Implements "path-splitting" optimisation that makes every node
     * point to its grandfather so each traversal reduces height of tree.
     *)
    method private find (x: tree): tree =
        let r = ref x in
        while !r.parent != !r do
            let next = !r.parent in
            !r.parent <- next.parent;
            r := next
        done;
        !r

    (* Find the root of the set containing 'x' - creating a new
     * set if not already known *)
    method private find_ident (x: ident): tree =
        let s = (match Bindings.find_opt x forest with
        | None ->
                let rec t = { parent = t; data = x; } in
                t
        | Some t ->
                self#find t
        ) in
        forest <- Bindings.add x s forest;
        s

    (* Find the canonical member of the set containing 'x' *)
    method canonicalize (x: ident): ident =
        let s = self#find_ident x in
        s.data

    (* Merge the sets containing 'x' and 'y' *)
    method merge (x: ident) (y: ident): unit =
        let x' = self#find_ident x in
        let y' = self#find_ident y in
        if x != y then y'.parent <- x'

    (* Optimization: short circuit every tree so that they all point directly at root *)
    method private normalize: unit =
        forest <- Bindings.map (self#find) forest

    (* Return mapping from identifiers to the canonical representation of their
     * equivalence class
     *)
    method mapping: ident Bindings.t =
        self#normalize;
        Bindings.map (fun t -> (self#find t).data) forest

    (* Construct equivalence classes for each canonical member of a class.
     *
     * The implementation of this could be made more efficient by adding
     * pointers to trees so that we can map each canonical member to a
     * tree containing all the nodes that point to it.
     * But this implementation just does a linear scan over all the members
     * of the forest.
     *)
    method classes: IdentSet.t Bindings.t =
        Bindings.fold (fun k v -> addToBindingSet v k) self#mapping Bindings.empty

    (* Print equivalence classes adding a prefix at the start of every line of
     * output.
     *)
    method pp (prefix: string): unit =
        Bindings.iter (fun v vs ->
            Printf.printf "%s%s -> {" prefix (pprint_ident v);
            IdentSet.iter (fun w -> Printf.printf " %s" (pprint_ident w)) vs;
            Printf.printf "}\n";
        ) self#classes
end


(****************************************************************)
(** {1 AST Transformation Utilities}                            *)
(****************************************************************)

(****************************************************************)
(** {2 Calculating free variables of expressions and types}     *)
(****************************************************************)

class freevarClass = object
    inherit nopAslVisitor

    val mutable fvs = IdentSet.empty
    method result = fvs
    method vvar x =
        fvs <- IdentSet.add x fvs;
        SkipChildren
end

let rec fv_expr (x: expr): IdentSet.t =
    let fv = new freevarClass in
    ignore (visit_expr (fv :> aslVisitor) x);
    fv#result

let rec fv_type (x: ty): IdentSet.t =
    let fv = new freevarClass in
    ignore (visit_type (fv :> aslVisitor) x);
    fv#result

let fv_args (atys: (ty * ident) list): IdentSet.t =
    unionSets (List.map (fun (ty, _) -> fv_type ty) atys)

let fv_sformal (x: sformal): IdentSet.t =
    (match x with
    | Formal_In(ty,v) -> fv_type ty
    | Formal_InOut(ty,v) -> fv_type ty
    )

let fv_sformals (atys: sformal list): IdentSet.t =
    unionSets (List.map fv_sformal atys)


(****************************************************************)
(** {2 Substitutions}                                           *)
(****************************************************************)

(** Performing variable substitutions in expressions and types

    Note that it does not replace type constructors, global constants
    or enumerations in patterns, array indexes and types so this is
    limited to replacing local variables.
    It also does not replace variables used as l-expressions though
    that it easily changed if we think it should.               *)
class substClass (s: expr Bindings.t) = object
    inherit nopAslVisitor
    method vexpr x =
        (match x with
        | Expr_Var v ->
                (match Bindings.find_opt v s with
                | Some r -> ChangeTo r
                | None -> DoChildren
                )
        | _ -> DoChildren
        )
end

let rec subst_expr (s: expr Bindings.t) (x: expr): expr =
    let subst = new substClass s in
    visit_expr subst x

let rec subst_lexpr (s: expr Bindings.t) (x: lexpr): lexpr =
    let subst = new substClass s in
    visit_lexpr subst x

let rec subst_slice (s: expr Bindings.t) (x: slice): slice =
    let subst = new substClass s in
    visit_slice subst x

let rec subst_type (s: expr Bindings.t) (x: ty): ty =
    let subst = new substClass s in
    visit_type subst x


(** More flexible substitution class - takes a function instead
    of a binding set.
 *)
class substFunClass (replace: ident -> expr option) = object
    inherit nopAslVisitor
    method vexpr x =
        (match x with
        | Expr_Var v ->
                (match replace v with
                | Some r -> ChangeTo r
                | None -> DoChildren
                )
        | _ -> DoChildren
        )
end

(****************************************************************)
(** {2 Expression transformation}                               *)
(****************************************************************)

(** Expression transformation class

    Applies replace function to any subexpression.
    (Especially useful for expressions in types)                *)
class replaceExprClass (replace: expr -> expr option) = object
    inherit nopAslVisitor
    method vexpr x =
        (match replace x with
        | Some r -> ChangeTo r
        | None -> SkipChildren
        )
end

(****************************************************************)
(** {2 Resugaring}                                              *)
(****************************************************************)

(** Resugaring transform

    The typechecker desugars infix syntax to make it absolutely explicit
    what it means.  This is good for tools but bad for humans.

    This transformation re-introduces the infix syntax - the intention
    being that you might use this in error messages.
    It also deletes type parameters - so this is (more or less)
    the reverse of typechecking.                                *)
class resugarClass (ops: AST.binop Bindings.t) = object (self)
    inherit nopAslVisitor
    method vexpr x =
        (match x with
        | Expr_TApply(f, tys, args) ->
                let args' = List.map (visit_expr (self :> aslVisitor)) args in
                (match (Bindings.find_opt f ops, args') with
                | (Some op, [a; b]) -> ChangeTo (Expr_Binop(a, op, b))
                (* | (Some op, [a]) -> ChangeTo (Expr_Unop(op, a)) *)
                | _ -> ChangeTo (Expr_TApply(f, [], args'))
                )
        | _ ->
                DoChildren
        )
end

let rec resugar_expr (ops: AST.binop Bindings.t) (x: expr): expr =
    let resugar = new resugarClass ops in
    visit_expr resugar x

let rec resugar_type (ops: AST.binop Bindings.t) (x: AST.ty): AST.ty =
    let resugar = new resugarClass ops in
    visit_type resugar x

(****************************************************************)
(** {2 Pretty printing wrappers}                                *)
(****************************************************************)

let pp_type  (x: ty):    string = Utils.to_string (PP.pp_ty    x)
let pp_expr  (x: expr):  string = Utils.to_string (PP.pp_expr  x)
let pp_lexpr (x: lexpr): string = Utils.to_string (PP.pp_lexpr x)
let pp_stmt  (x: stmt):  string = Utils.to_string (PP.pp_stmt  x)


(****************************************************************)
(** {2 Misc}                                                    *)
(****************************************************************)

(** Length of bitstring or mask literal.

    ASL bit and mask literals allow spaces to be included - these
    do not count towards the length of the literal.
 *)
let masklength (x: string): int =
    let r = ref 0 in
    String.iter (function ' ' -> () | _ -> r := !r + 1) x;
    !r

(****************************************************************
 * End
 ****************************************************************)
