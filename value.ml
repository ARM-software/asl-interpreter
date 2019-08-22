(****************************************************************
 * ASL interpreter values
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** ASL interpreter values *)

open Primops

module AST = Asl_ast
open Asl_utils

(****************************************************************)
(** {2 Values}                                                  *)
(****************************************************************)

(** This union type is for use in an interpreter *)

type value =
    | VBool   of bool   (* optimised special case of VEnum *)
    | VEnum   of (AST.ident * int)
    | VInt    of bigint
    | VReal   of real
    | VBits   of bitvector
    | VMask   of mask
    | VString of string
    | VExc    of (AST.l * exc)
    | VTuple  of (value list)
    | VRecord of (value Bindings.t)
    | VArray  of (value ImmutableArray.t * value)
    | VRAM    of ram
    | VUninitialized (* initial value of scalars with no explicit initialization *)


(****************************************************************)
(** {2 Exceptions thrown by interpreter}                        *)
(****************************************************************)

exception Return    of value option
exception EvalError of (AST.l * string)
exception Throw     of (AST.l * exc)


(****************************************************************)
(** {2 Printer for values}                                      *)
(****************************************************************)

let rec pp_value (x: value): string =
    (match x with
    | VBool   b       -> prim_cvt_bool_str b
    | VEnum   (e, _)  -> AST.pprint_ident e
    | VInt    i       -> prim_cvt_int_decstr i
    | VReal   r       -> prim_cvt_real_str r
    | VBits   b       -> prim_cvt_bits_str (Z.of_int b.n) b
    | VMask   m       -> "todo: mask"
    | VString s       -> "\"" ^ s ^ "\""
    | VExc (loc, exc) ->
        let msg = (match exc with
            | Exc_ConstrainedUnpredictable -> "ConstrainedUnpredictable"
            | Exc_ExceptionTaken           -> "ExceptionTaken"
            | Exc_ImpDefined s             -> "ImpDefined" ^ s
            | Exc_SEE s                    -> "SEE" ^ s
            | Exc_Undefined                -> "Undefined"
            | Exc_Unpredictable            -> "Unpredictable"
        ) in
        "Exception " ^ msg ^ " at " ^ Asl_ast.pp_loc loc
    | VTuple  vs -> "(" ^ String.concat ", " (List.map pp_value vs) ^ ")"
    | VRecord fs ->
        let fs' = List.map (fun (f, v) -> "."^ AST.pprint_ident f ^" = "^ pp_value v) (Bindings.bindings fs)
        in
        "{" ^ String.concat ", " fs' ^ "}"
    | VArray (a, _) ->
        let vs = List.map (fun (i, v) -> string_of_int i ^":"^ pp_value v) (ImmutableArray.bindings a) in
        "[" ^ String.concat ", " vs ^ "]"
    | VRAM _ -> "RAM"
    | VUninitialized -> "UNINITIALIZED"
    )


(****************************************************************)
(** {2 Functions on values}                                     *)
(****************************************************************)

let from_bool (x: bool): value = VBool x

let to_bool (loc: AST.l) (x: value): bool =
    (match x with
    | VBool b -> b
    | _ -> raise (EvalError (loc, "boolean expected"))
    )

let to_integer (loc: AST.l) (x: value): bigint =
    (match x with
    | VInt i -> i
    | _ -> raise (EvalError (loc, "integer expected"))
    )

(* todo: this should raise an exception if out of range *)
let to_int (loc: AST.l) (x: value): int =
    (match x with
    | VInt i -> Z.to_int i
    | _ -> raise (EvalError (loc, "integer expected"))
    )

let to_bits (loc: AST.l) (x: value): bitvector =
    (match x with
    | VBits b -> b
    | _ -> raise (EvalError (loc, "bits expected"))
    )

let to_mask (loc: AST.l) (x: value): mask =
    (match x with
    | VMask m -> m
    | _ -> raise (EvalError (loc, "mask expected"))
    )

let to_string (loc: AST.l) (x: value): string =
    (match x with
    | VString s -> s
    | _ -> raise (EvalError (loc, "string expected"))
    )

let to_exc (loc: AST.l) (x: value): (AST.l * exc) =
    (match x with
    | VExc e -> e
    | _ -> raise (EvalError (loc, "exception expected"))
    )

let to_tuple (xs: value list): value = VTuple xs

let of_tuple (loc: AST.l) (x: value): value list =
    (match x with
    | VTuple xs -> xs
    | _ -> raise (EvalError (loc, "tuple expected"))
    )

let mkrecord (fs: (AST.ident * value) list): value =
    VRecord (mk_bindings fs)

let get_field (loc: AST.l) (x: value) (f: AST.ident): value =
    (match x with
    | VRecord fs -> Bindings.find f fs
    | _ -> raise (EvalError (loc, "record expected"))
    )

let set_field (loc: AST.l) (x: value) (f: AST.ident) (v: value): value =
    (match x with
    | VRecord fs -> VRecord (Bindings.add f v fs)
    | _ -> raise (EvalError (loc, "record expected"))
    )

let empty_array (d: value): value =
    VArray (prim_empty_array, d)

let get_array (loc: AST.l) (a: value) (i: value): value =
    (match (a, i) with
    | (VArray (x, d), VInt  i') -> prim_read_array x (Z.to_int i') d
    | (VArray (x, d), VEnum i') -> prim_read_array x (snd i') d
    | (VArray (x, d), _) -> raise (EvalError (loc, "array index expected"))
    | _ -> raise (EvalError (loc, "array expected"))
    )

let set_array (loc: AST.l) (a: value) (i: value) (v: value): value =
    (match (a, i) with
    | (VArray (x, d), VInt  i') -> VArray (prim_write_array x (Z.to_int i') v, d)
    | (VArray (x, d), VEnum i') -> VArray (prim_write_array x (snd i') v, d)
    | (VArray (x, d), _) -> raise (EvalError (loc, "array index expected"))
    | _ -> raise (EvalError (loc, "array expected"))
    )

(** Delete all characters matching 'c' from string 'x' *)
let drop_chars (x: string) (c: char): string =
    (* First calculate final length *)
    let len = ref 0 in
    String.iter (fun t -> if t <> c then len := !len + 1) x;

    (* search for next character not matching c *)
    let i = ref 0 in
    let rec next_char (_: int): char =
        let r = String.get x !i in
        i := !i + 1;
        if r = c then next_char 0 else r
    in

    (* create result *)
    String.init !len next_char


let from_intLit (x: AST.intLit): value = VInt (Z.of_string x)
let from_hexLit (x: AST.hexLit): value = VInt (Z.of_string_base 16 (drop_chars x '_'))

let from_realLit (x: AST.realLit): value =
    let pt          = String.index x '.' in
    let fracsz      = String.length x - pt - 1 in
    let intpart     = String.sub x 0 pt in
    let frac        = String.sub x (pt+1) fracsz in
    let numerator   = Z.of_string (intpart ^ frac) in
    let denominator = Z.pow (Z.of_int 10) fracsz in
    VReal (Q.make numerator denominator)

let from_bitsLit (x: AST.bitsLit): value =
    let x' = drop_chars x ' ' in
    VBits (mkBits (String.length x') (Z.of_string_base 2 x'))

let from_maskLit (x: AST.maskLit): value =
    let x' = drop_chars x ' ' in
    let n = String.length x' in
    let v = String.map (function 'x' -> '0' | c -> c) x' in
    let m = String.map (function 'x' -> '0' | c -> '1') x' in
    VMask (mkMask n (Z.of_string_base 2 v) (Z.of_string_base 2 m))

let from_stringLit (x: string): value = VString x


(****************************************************************)
(** {2 Primop dispatch on values}                               *)
(****************************************************************)

(** Returns None iff function does not exist or arguments have wrong type *)

let eval_prim (f: string) (tvs: value list) (vs: value list): value option =
    ( match (f, tvs, vs) with
    | ("eq_enum",           [      ], [VEnum x; VEnum y    ])     -> Some (VBool   (snd x =  snd y))
    | ("ne_enum",           [      ], [VEnum x; VEnum y    ])     -> Some (VBool   (snd x <> snd y))
    | ("eq_bool",           [      ], [VBool x; VBool y    ])     -> Some (VBool   (prim_eq_bool    x y))
    | ("ne_bool",           [      ], [VBool x; VBool y    ])     -> Some (VBool   (prim_ne_bool    x y))
    | ("equiv_bool",        [      ], [VBool x; VBool y    ])     -> Some (VBool   (prim_equiv_bool x y))
    | ("not_bool",          [      ], [VBool x             ])     -> Some (VBool   (prim_not_bool   x))
    | ("eq_int",            [      ], [VInt  x; VInt  y    ])     -> Some (VBool   (prim_eq_int     x y))
    | ("ne_int",            [      ], [VInt  x; VInt  y    ])     -> Some (VBool   (prim_ne_int     x y))
    | ("le_int",            [      ], [VInt  x; VInt  y    ])     -> Some (VBool   (prim_le_int     x y))
    | ("lt_int",            [      ], [VInt  x; VInt  y    ])     -> Some (VBool   (prim_lt_int     x y))
    | ("ge_int",            [      ], [VInt  x; VInt  y    ])     -> Some (VBool   (prim_ge_int     x y))
    | ("gt_int",            [      ], [VInt  x; VInt  y    ])     -> Some (VBool   (prim_gt_int     x y))
    | ("is_pow2_int",       [      ], [VInt  x             ])     -> Some (VBool   (prim_is_pow2_int x))
    | ("neg_int",           [      ], [VInt  x             ])     -> Some (VInt    (prim_neg_int    x))
    | ("add_int",           [      ], [VInt  x; VInt  y    ])     -> Some (VInt    (prim_add_int    x y))
    | ("sub_int",           [      ], [VInt  x; VInt  y    ])     -> Some (VInt    (prim_sub_int    x y))
    | ("shl_int",           [      ], [VInt  x; VInt  y    ])     -> Some (VInt    (prim_shl_int    x y))
    | ("shr_int",           [      ], [VInt  x; VInt  y    ])     -> Some (VInt    (prim_shr_int    x y))
    | ("mul_int",           [      ], [VInt  x; VInt  y    ])     -> Some (VInt    (prim_mul_int    x y))
    | ("zdiv_int",          [      ], [VInt  x; VInt  y    ])     -> Some (VInt    (prim_zdiv_int   x y))
    | ("zrem_int",          [      ], [VInt  x; VInt  y    ])     -> Some (VInt    (prim_zrem_int   x y))
    | ("fdiv_int",          [      ], [VInt  x; VInt  y    ])     -> Some (VInt    (prim_fdiv_int   x y))
    | ("frem_int",          [      ], [VInt  x; VInt  y    ])     -> Some (VInt    (prim_frem_int   x y))
    | ("mod_pow2_int",      [      ], [VInt  x; VInt  y    ])     -> Some (VInt    (prim_mod_pow2_int x y))
    | ("align_int",         [      ], [VInt  x; VInt  y    ])     -> Some (VInt    (prim_align_int    x y))
    | ("pow2_int",          [      ], [VInt  x             ])     -> Some (VInt    (prim_pow2_int     x))
    | ("pow_int_int",       [      ], [VInt  x; VInt  y    ])     -> Some (VInt    (prim_pow_int_int  x y))
    | ("cvt_int_real",      [      ], [VInt x              ])     -> Some (VReal   (prim_cvt_int_real x))
    | ("eq_real",           [      ], [VReal x; VReal y    ])     -> Some (VBool   (prim_eq_real x y))
    | ("ne_real",           [      ], [VReal x; VReal y    ])     -> Some (VBool   (prim_ne_real x y))
    | ("le_real",           [      ], [VReal x; VReal y    ])     -> Some (VBool   (prim_le_real x y))
    | ("lt_real",           [      ], [VReal x; VReal y    ])     -> Some (VBool   (prim_lt_real x y))
    | ("ge_real",           [      ], [VReal x; VReal y    ])     -> Some (VBool   (prim_ge_real x y))
    | ("gt_real",           [      ], [VReal x; VReal y    ])     -> Some (VBool   (prim_gt_real x y))
    | ("add_real",          [      ], [VReal x; VReal y    ])     -> Some (VReal   (prim_add_real x y))
    | ("neg_real",          [      ], [VReal x             ])     -> Some (VReal   (prim_neg_real x))
    | ("sub_real",          [      ], [VReal x; VReal y    ])     -> Some (VReal   (prim_sub_real x y))
    | ("mul_real",          [      ], [VReal x; VReal y    ])     -> Some (VReal   (prim_mul_real x y))
    | ("divide_real",       [      ], [VReal x; VReal y    ])     -> Some (VReal   (prim_div_real x y))
    | ("pow2_real",         [      ], [VInt  x             ])     -> Some (VReal   (prim_pow2_real x))
    | ("round_tozero_real", [      ], [VReal x             ])     -> Some (VInt    (prim_round_tozero_real x))
    | ("round_down_real",   [      ], [VReal x             ])     -> Some (VInt    (prim_round_down_real x))
    | ("round_up_real",     [      ], [VReal x             ])     -> Some (VInt    (prim_round_up_real x))
    | ("sqrt_real",         [      ], [VReal x; VReal y    ])     -> Some (VReal   (prim_sqrt_real x))
    | ("cvt_int_bits",      [_     ], [VInt  x; VInt  n    ])     -> Some (VBits   (prim_cvt_int_bits n x))
    | ("cvt_bits_sint",     [VInt n], [VBits x             ])     -> Some (VInt    (prim_cvt_bits_sint x))
    | ("cvt_bits_uint",     [VInt n], [VBits x             ])     -> Some (VInt    (prim_cvt_bits_uint x))
    | ("in_mask",           [VInt n], [VBits x; VMask y    ])     -> Some (VBool   (prim_in_mask x y))
    | ("notin_mask",        [VInt n], [VBits x; VMask y    ])     -> Some (VBool   (prim_notin_mask x y))
    | ("eq_bits",           [VInt n], [VBits x; VBits y    ])     -> Some (VBool   (prim_eq_bits x y))
    | ("ne_bits",           [VInt n], [VBits x; VBits y    ])     -> Some (VBool   (prim_ne_bits x y))
    | ("add_bits",          [VInt n], [VBits x; VBits y    ])     -> Some (VBits   (prim_add_bits x y))
    | ("sub_bits",          [VInt n], [VBits x; VBits y    ])     -> Some (VBits   (prim_sub_bits x y))
    | ("mul_bits",          [VInt n], [VBits x; VBits y    ])     -> Some (VBits   (prim_mul_bits x y))
    | ("and_bits",          [VInt n], [VBits x; VBits y    ])     -> Some (VBits   (prim_and_bits x y))
    | ("or_bits",           [VInt n], [VBits x; VBits y    ])     -> Some (VBits   (prim_or_bits x y))
    | ("eor_bits",          [VInt n], [VBits x; VBits y    ])     -> Some (VBits   (prim_eor_bits x y))
    | ("not_bits",          [VInt n], [VBits x             ])     -> Some (VBits   (prim_not_bits x))
    | ("zeros_bits",        [VInt n], [                    ])     -> Some (VBits   (prim_zeros_bits n))
    | ("ones_bits",         [VInt n], [                    ])     -> Some (VBits   (prim_ones_bits n))
    | ("replicate_bits",    [_; _  ], [VBits x; VInt y     ])     -> Some (VBits   (prim_replicate_bits x y))
    | ("append_bits",       [VInt m; VInt n], [VBits x; VBits y]) -> Some (VBits   (prim_append_bits x y))
    | ("eq_str",            [      ], [VString x; VString y])     -> Some (VBool   (prim_eq_str x y))
    | ("ne_str",            [      ], [VString x; VString y])     -> Some (VBool   (prim_ne_str x y))
    | ("append_str_str",    [      ], [VString x; VString y])     -> Some (VString (prim_append_str x y))
    | ("cvt_int_hexstr",    [      ], [VInt x              ])     -> Some (VString (prim_cvt_int_hexstr x))
    | ("cvt_int_decstr",    [      ], [VInt x              ])     -> Some (VString (prim_cvt_int_decstr x))
    | ("cvt_bool_str",      [      ], [VBool x             ])     -> Some (VString (prim_cvt_bool_str x))
    | ("cvt_bits_str",      [_     ], [VInt n;    VBits x  ])     -> Some (VString (prim_cvt_bits_str n x))
    | ("cvt_real_str",      [      ], [VReal x             ])     -> Some (VString (prim_cvt_real_str x))
    | ("is_cunpred_exc",    [      ], [VExc (_, ex)        ])     -> Some (VBool   (prim_is_cunpred_exc ex))
    | ("is_exctaken_exc",   [      ], [VExc (_, ex)        ])     -> Some (VBool   (prim_is_exctaken_exc ex))
    | ("is_impdef_exc",     [      ], [VExc (_, ex)        ])     -> Some (VBool   (prim_is_impdef_exc ex))
    | ("is_see_exc",        [      ], [VExc (_, ex)        ])     -> Some (VBool   (prim_is_see_exc ex))
    | ("is_undefined_exc",  [      ], [VExc (_, ex)        ])     -> Some (VBool   (prim_is_undefined_exc ex))
    | ("is_unpred_exc",     [      ], [VExc (_, ex)        ])     -> Some (VBool   (prim_is_unpred_exc ex))

    (* The remaining primops all have side effects *)
    | ("ram_init",          _,        [VInt a; VInt n; VRAM ram; VBits i])          -> Some (prim_init_ram a n ram i; VTuple [])
    | ("ram_read",          _,        [VInt a; VInt n; VRAM ram; VBits i])          -> Some (VBits (prim_read_ram a n ram i.v))
    | ("ram_write",         _,        [VInt a; VInt n; VRAM ram; VBits i; VBits x]) -> Some (prim_write_ram a n ram i.v x; VTuple [])

    | ("trace_memory_read",  _,       [VInt a; VInt n; VRAM ram; VInt  i; VBits x]) -> Some (prim_trace_memory_write a n ram i x; VTuple [])
    | ("trace_memory_write", _,       [VInt a; VInt n; VRAM ram; VInt  i; VBits x]) -> Some (prim_trace_memory_read  a n ram i x; VTuple [])
    | ("trace_event",        _,       [VString s                                 ]) -> Some (prim_trace_event s; VTuple [])

    | ("asl_file_open",      _,       [VString name; VString mode]) -> Some (VInt (prim_open_file name mode))
    | ("asl_file_write",     _,       [VInt fd;      VString data]) -> Some (prim_write_file fd data; VTuple [])
    | ("asl_file_getc",      _,       [VInt fd                   ]) -> Some (VInt (prim_getc_file fd))
    | ("print_str",          _,       [VString s                 ]) -> Some (prim_print_str  s; VTuple [])
    | ("print_char",         _,       [VInt c                    ]) -> Some (prim_print_char c; VTuple [])

    (* No function matches *)
    | _ -> None
    )


(****************************************************************)
(** {2 Utility functions on Values}                             *)
(****************************************************************)

let extract_bits (loc: AST.l) (x: value) (i: value) (w: value): value =
    VBits (prim_extract (to_bits loc x) (to_integer loc i) (to_integer loc w))

let extract_bits' (loc: AST.l) (x: value) (i: int) (w: int): value =
    VBits (prim_extract (to_bits loc x) (Z.of_int i) (Z.of_int w))

let extract_bits'' (loc: AST.l) (x: value) (i: value) (w: value): value =
    (match x with
    | VInt(x')  -> VBits (prim_extract_int x' (to_integer loc i) (to_integer loc w))
    | VBits(x') -> VBits (prim_extract x'     (to_integer loc i) (to_integer loc w))
    | _ -> raise (EvalError (loc, "bits or integer expected"))
    )

let insert_bits (loc: AST.l) (x: value) (i: value) (w: value) (y: value): value =
    VBits (prim_insert (to_bits loc x) (to_integer loc i) (to_integer loc w) (to_bits loc y))

let insert_bits' (loc: AST.l) (x: value) (i: int) (w: int) (y: value): value =
    VBits (prim_insert (to_bits loc x) (Z.of_int i) (Z.of_int w) (to_bits loc y))

let rec eval_eq (loc: AST.l) (x: value) (y: value): bool =
    (match (x, y) with
    | (VBool   x', VBool   y') -> prim_eq_bool x' y'
    | (VEnum   x', VEnum   y') -> snd x' = snd y'
    | (VInt    x', VInt    y') -> prim_eq_int x' y'
    | (VReal   x', VReal   y') -> prim_eq_real x' y'
    | (VBits   x', VBits   y') -> prim_eq_bits x' y'
    | (VString x', VString y') -> String.equal x' y'
    | (VTuple  xs, VTuple  ys) -> List.for_all2 (eval_eq loc) xs ys
    | _ -> raise (EvalError (loc, "matchable types expected"))
    )

let eval_leq (loc: AST.l) (x: value) (y: value): bool =
    (match (x, y) with
    | (VInt x', VInt y') -> prim_le_int x' y'
    | _ -> raise (EvalError (loc, "integer expected"))
    )

let eval_eq_int (loc: AST.l) (x: value) (y: value): bool =
    prim_eq_int  (to_integer loc x) (to_integer loc y)

let eval_eq_bits (loc: AST.l) (x: value) (y: value): bool =
    prim_eq_bits (to_bits loc x) (to_bits loc y)

(* todo: should m be a value or a mask? *)
let eval_inmask (loc: AST.l) (x: value) (m: value): bool =
    prim_in_mask (to_bits loc x) (to_mask loc m)

let eval_add_int (loc: AST.l) (x: value) (y: value): value =
    VInt (prim_add_int (to_integer loc x) (to_integer loc y))

let eval_sub_int (loc: AST.l) (x: value) (y: value): value =
    VInt (prim_sub_int (to_integer loc x) (to_integer loc y))

let eval_concat (loc: AST.l) (xs: value list): value =
    let xs' = List.map (to_bits loc) xs in
    VBits (List.fold_left prim_append_bits empty_bits xs')


(****************************************************************)
(** {2 Unknown handling}                                        *)
(****************************************************************)

(** We might want to change this in the future to model the expected
    non-determinism in the spec.
    And we might want to augment this with some form of support for
    uninitialized values (which would ideally trigger an error).
 *)

let eval_unknown_bits (wd: Primops.bigint): value =
    VBits (Primops.mkBits (Z.to_int wd) Z.zero)

let eval_unknown_ram (a: Primops.bigint): value =
    VRAM (Primops.init_ram (char_of_int 0))

let eval_unknown_integer (_: unit): value = VInt Z.zero
let eval_unknown_real    (_: unit): value = VReal Q.zero
let eval_unknown_string  (_: unit): value = VString "<UNKNOWN string>"

(****************************************************************
 * End
 ****************************************************************)
