(****************************************************************
 * ASL primitive types and operations
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** ASL primitive types and operations *)

module AST  = Asl_ast

(****************************************************************)
(** {2 Boolean primops}                                         *)
(****************************************************************)

let prim_eq_bool    (x: bool) (y: bool): bool = x = y
let prim_ne_bool    (x: bool) (y: bool): bool = x <> y
let prim_and_bool   (x: bool) (y: bool): bool = x && y
let prim_or_bool    (x: bool) (y: bool): bool = x || y
let prim_equiv_bool (x: bool) (y: bool): bool = x = y
let prim_not_bool   (x: bool): bool           = not x


(****************************************************************)
(** {2 Integer primops}                                         *)
(****************************************************************)

type bigint = Z.t

let prim_eq_int (x: bigint) (y: bigint): bool = Z.equal x y
let prim_ne_int (x: bigint) (y: bigint): bool = not (Z.equal x y)
let prim_le_int (x: bigint) (y: bigint): bool = Z.leq x y
let prim_lt_int (x: bigint) (y: bigint): bool = Z.lt  x y
let prim_ge_int (x: bigint) (y: bigint): bool = Z.geq x y
let prim_gt_int (x: bigint) (y: bigint): bool = Z.gt  x y
let prim_is_pow2_int (x: bigint): bool = Z.equal (Z.logand x (Z.sub x Z.one)) Z.zero
let prim_neg_int (x: bigint): bigint             = Z.neg         x
let prim_add_int (x: bigint) (y: bigint): bigint = Z.add         x y
let prim_sub_int (x: bigint) (y: bigint): bigint = Z.sub         x y
let prim_shl_int (x: bigint) (y: bigint): bigint = Z.shift_left  x (Z.to_int y)
let prim_shr_int (x: bigint) (y: bigint): bigint = Z.shift_right x (Z.to_int y)
let prim_mul_int (x: bigint) (y: bigint): bigint = Z.mul         x y

let prim_zdiv_int (x: bigint) (y: bigint): bigint = Z.div x y
let prim_zrem_int (x: bigint) (y: bigint): bigint = Z.rem x y
let prim_fdiv_int (x: bigint) (y: bigint): bigint = Z.fdiv  x y
let prim_frem_int (x: bigint) (y: bigint): bigint = Z.sub x (Z.mul y (Z.fdiv x y))
let prim_mod_pow2_int (x: bigint) (y: bigint): bigint =
    let mask = Z.sub (Z.shift_left Z.one (Z.to_int y)) Z.one in
    Z.logand x mask
let prim_align_int (x: bigint) (y: bigint): bigint =
    let y' = Z.to_int y in
    (* todo: not very efficient *)
    Z.shift_left (Z.shift_right_trunc x y') y'

let prim_pow2_int (x: bigint): bigint = Z.shift_left Z.one (Z.to_int x)

let prim_pow_int_int (x: bigint) (y: bigint): bigint =
    let y' = Z.to_int y in
    assert (y' >= 0);
    Z.pow x y'


(****************************************************************)
(** {2 Real primops}                                            *)
(****************************************************************)

type real   = Q.t

let prim_cvt_int_real (x: bigint): real     = Q.of_bigint x
let prim_eq_real  (x: real) (y: real): bool = Q.equal x y
let prim_ne_real  (x: real) (y: real): bool = not (Q.equal x y)
let prim_le_real  (x: real) (y: real): bool = Q.leq x y
let prim_lt_real  (x: real) (y: real): bool = Q.lt  x y
let prim_ge_real  (x: real) (y: real): bool = Q.geq x y
let prim_gt_real  (x: real) (y: real): bool = Q.gt  x y
let prim_neg_real (x: real): real           = Q.neg x
let prim_add_real (x: real) (y: real): real = Q.add x y
let prim_sub_real (x: real) (y: real): real = Q.sub x y
let prim_mul_real (x: real) (y: real): real = Q.mul x y
let prim_div_real (x: real) (y: real): real = Q.div x y

let prim_pow2_real         (x: bigint): real =
    let x' = Z.to_int x in
    if x' >= 0 then Q.mul_2exp Q.one x' else Q.div_2exp Q.one (-x')

let prim_round_tozero_real (x: real): bigint = Q.to_bigint x

let prim_round_down_real   (x: real): bigint =
    if Q.sign x >= 0 then begin
        Q.to_bigint x
    end else if Z.equal Z.one (Q.den x) then begin (* exact int *)
        Q.to_bigint x
    end else begin
        Z.sub Z.one (Q.to_bigint x)
    end

let prim_round_up_real     (x: real): bigint =
    if Q.sign x <= 0 then begin
        Q.to_bigint x
    end else if Z.equal Z.one (Q.den x) then begin (* exact int *)
        Q.to_bigint x
    end else begin
        Z.add Z.one (Q.to_bigint x)
    end

let prim_sqrt_real         (x: real): real = failwith "prim_sqrt_real"


(****************************************************************)
(** {2 Bitvector primops}                                       *)
(****************************************************************)

(** Invariants:
    - the bigint part of a bitvector is positive
    - the bigint part of an N-bit bitvector is less than 2^N
 *)

type bitvector = { n: int; v: Z.t }

let empty_bits = { n = 0; v = Z.zero }

(* primary way of creating bitvector satisfying invariants *)
let mkBits (n: int) (v: bigint): bitvector = (
    assert (n >= 0);
    if n = 0 then (* workaround: ZArith library doesn't like zero-length extracts *)
        { n; v = Z.zero }
    else
        { n; v = Z.extract v 0 n }
)

(* utility function for use in implementing binary operators
 * that checks that size of left operand and of right operand were the same
 *)
let mkBits2 (n1: int) (n2: int) (v: bigint): bitvector = (
    assert (n1 = n2);
    assert (n1 >= 0);
    if n1 = 0 then (* workaround: ZArith library doesn't like zero-length extracts *)
        { n = n1; v = Z.zero }
    else
        { n = n1; v = Z.extract v 0 n1 }
)

let prim_length_bits (x: bitvector): int = x.n

let prim_cvt_int_bits (n: bigint) (i: bigint): bitvector = (
    assert (Z.geq n Z.zero);
    let n' = Z.to_int n in
    { n = n'; v = Z.extract i 0 n' }
)

let prim_cvt_bits_sint (x: bitvector): bigint = Z.signed_extract x.v 0 x.n
let prim_cvt_bits_uint (x: bitvector): bigint = Z.extract x.v 0 x.n

let prim_eq_bits  (x: bitvector) (y: bitvector): bool = assert (x.n = y.n); Z.equal x.v y.v
let prim_ne_bits  (x: bitvector) (y: bitvector): bool = assert (x.n = y.n); not (Z.equal x.v y.v)
let prim_add_bits (x: bitvector) (y: bitvector): bitvector = mkBits2 x.n y.n (Z.add x.v y.v)
let prim_sub_bits (x: bitvector) (y: bitvector): bitvector = mkBits2 x.n y.n (Z.sub x.v y.v)

(* Note that because mul_bits produces the same size result as its inputs, the
 * result is the same whether you consider bits to be signed or unsigned
 *)
let prim_mul_bits (x: bitvector) (y: bitvector): bitvector = mkBits2 x.n y.n (Z.mul x.v y.v)

let prim_and_bits (x: bitvector) (y: bitvector): bitvector = mkBits x.n (Z.logand x.v y.v)
let prim_or_bits  (x: bitvector) (y: bitvector): bitvector = mkBits x.n (Z.logor  x.v y.v)
let prim_eor_bits (x: bitvector) (y: bitvector): bitvector = mkBits x.n (Z.logxor x.v y.v)
let prim_not_bits (x: bitvector): bitvector = mkBits x.n (Z.lognot x.v)

let prim_zeros_bits (x: bigint): bitvector = mkBits (Z.to_int x) Z.zero
let prim_ones_bits  (x: bigint): bitvector = mkBits (Z.to_int x) Z.minus_one
let prim_append_bits (x: bitvector) (y: bitvector): bitvector = mkBits (x.n+y.n) (Z.logor (Z.shift_left x.v y.n) y.v)

let prim_replicate_bits (x: bitvector) (y: bigint): bitvector =
    (* Tail recursive helper to calculate "x : ... : x : r" with c copies of x *)
    let rec power x c r =
        if c = 0 then r
        else
            let r' = if (c land 1) = 0 then r else prim_append_bits x r in
            power (prim_append_bits x x) (c / 2) r'
    in
    assert (Z.sign y >= 0);
    power x (Z.to_int y) empty_bits

let prim_extract (x: bitvector) (i: bigint) (w: bigint): bitvector =
    let i' = Z.to_int i in
    let w' = Z.to_int w in
    assert (0 <= i');
    assert (0 <= w');
    assert (i' + w' <= x.n);
    mkBits w' (Z.extract x.v i' w')

let prim_extract_int (x: Z.t) (i: bigint) (w: bigint): bitvector =
    let i' = Z.to_int i in
    let w' = Z.to_int w in
    assert (0 <= i');
    assert (0 <= w');
    mkBits w' (Z.extract x i' w')

let prim_insert (x: bitvector) (i: bigint) (w: bigint) (y: bitvector): bitvector =
    let i' = Z.to_int i in
    let w' = Z.to_int w in
    assert (0 <= i');
    assert (0 <= w');
    assert (i' + w' <= x.n);
    assert (w' = y.n);
    let msk = (Z.sub (Z.shift_left Z.one (i'+w')) (Z.shift_left Z.one i')) in
    let nmsk = Z.lognot msk in
    let y' = Z.shift_left (Z.extract y.v 0 w') i' in
    mkBits x.n (Z.logor (Z.logand nmsk x.v) (Z.logand msk y'))


(****************************************************************)
(** {2 Mask primops}                                            *)
(****************************************************************)

type mask = { n: int; v: Z.t; m: Z.t }

let mkMask (n: int) (v: Z.t) (m: Z.t): mask =
    assert (Z.equal v (Z.logand v m));
    { n; v; m }

let prim_in_mask (x: bitvector) (m: mask): bool =
    Z.equal (Z.logand x.v m.m) m.v

let prim_notin_mask (x: bitvector) (m: mask): bool =
    not (prim_in_mask x m)


(****************************************************************)
(** {2 Exception primops}                                       *)
(****************************************************************)

type exc =
    | Exc_ConstrainedUnpredictable
    | Exc_ExceptionTaken
    | Exc_ImpDefined of string
    | Exc_SEE of string
    | Exc_Undefined
    | Exc_Unpredictable

let prim_is_cunpred_exc    (x: exc): bool = (match x with Exc_ConstrainedUnpredictable -> true | _ -> false)
let prim_is_exctaken_exc   (x: exc): bool = (match x with Exc_ExceptionTaken -> true | _ -> false)
let prim_is_impdef_exc     (x: exc): bool = (match x with Exc_ImpDefined _   -> true | _ -> false)
let prim_is_see_exc        (x: exc): bool = (match x with Exc_SEE _          -> true | _ -> false)
let prim_is_undefined_exc  (x: exc): bool = (match x with Exc_Undefined      -> true | _ -> false)
let prim_is_unpred_exc     (x: exc): bool = (match x with Exc_Unpredictable  -> true | _ -> false)


(****************************************************************)
(** {2 String primops}                                          *)
(****************************************************************)

let prim_eq_str         (x: string) (y: string): bool   = x = y
let prim_ne_str         (x: string) (y: string): bool   = x <> y
let prim_append_str     (x: string) (y: string): string = x ^ y
let prim_cvt_int_hexstr (x: bigint): string = Z.format "%x" x
let prim_cvt_int_decstr (x: bigint): string = Z.to_string x
let prim_cvt_bool_str   (x: bool): string = if x then "TRUE" else "FALSE"

let prim_cvt_bits_str   (n: bigint) (x: bitvector): string =
    if Z.equal n Z.zero then begin
        "''"
    end else begin
        let s = Z.format "%0b" x.v in
        let pad = String.make (Z.to_int n - String.length s) '0' in
        Z.to_string n ^ "'" ^ pad ^ s ^ "'"
    end

let prim_cvt_real_str   (x: real): string =
    let r = Q.to_string x in
    if String.contains r '/' then r else r ^ "/1"


(****************************************************************)
(** {2 Immutable Array type}                                    *)
(****************************************************************)

module Index = struct
    type t = int
    let compare x y = Stdlib.compare x y
end

module ImmutableArray = Map.Make(Index)

let prim_empty_array: 'a ImmutableArray.t =
    ImmutableArray.empty

let prim_read_array (x: 'a ImmutableArray.t) (i: int) (default: 'a): 'a =
    (match ImmutableArray.find_opt i x with
    | Some r -> r
    | None   -> default
    )

let prim_write_array (x: 'a ImmutableArray.t) (i: int) (v: 'a): 'a ImmutableArray.t =
    ImmutableArray.add i v x


(****************************************************************)
(** {2 Mutable RAM type}                                        *)
(****************************************************************)

(** RAM is implemented as a paged data structure and pages are
    allocated on demand and initialized with a specified default
    value.
 *)

module Pages = struct
    include Map.Make(struct
        type t = bigint
        let compare = Z.compare
    end)
end

type ram = {
    mutable contents: Bytes.t Pages.t;
    mutable default:  char
}

let logPageSize = 16
let pageSize    = 1 lsl logPageSize
let pageMask    = Z.of_int (pageSize - 1)

let pageIndexOfAddr  (a: bigint): bigint = Z.shift_right a logPageSize
let pageOffsetOfAddr (a: bigint): bigint = Z.logand      a pageMask

let init_ram (d: char): ram =
    { contents = Pages.empty; default = d }

let clear_ram (mem: ram) (d: char): unit =
    mem.contents <- Pages.empty;
    mem.default  <- d

let readByte_ram (mem: ram) (addr: bigint): char =
    let index  = pageIndexOfAddr  addr in
    let offset = pageOffsetOfAddr addr in
    (match Pages.find_opt index mem.contents with
    | Some bs -> Bytes.get bs (Z.to_int offset)
    | None    -> mem.default
    )

let writeByte_ram (mem: ram) (addr: bigint) (v: char): unit =
    let index  = pageIndexOfAddr  addr in
    let offset = pageOffsetOfAddr addr in
    let bs = (match Pages.find_opt index mem.contents with
    | Some bs ->
            bs
    | None ->
            let bs = Bytes.make pageSize mem.default in
            mem.contents <- Pages.add index bs mem.contents;
            bs
    ) in
    Bytes.set bs (Z.to_int offset) v

let prim_init_ram (asz: bigint) (dsz: bigint) (mem: ram) (init: bitvector): unit =
    clear_ram mem (char_of_int (Z.to_int init.v))

let prim_read_ram (asz: bigint) (dsz: bigint) (mem: ram) (addr: bigint): bitvector =
    let r = ref Z.zero in
    let rec read (i: int): unit =
        if i < (Z.to_int dsz) then
            let b = readByte_ram mem (Z.add addr (Z.of_int i)) in
            r := Z.logor (Z.shift_left (Z.of_int (int_of_char b)) (8 * i)) !r;
            read (i+1)
    in
    read 0;
    mkBits (8 * (Z.to_int dsz)) !r

let prim_write_ram (asz: bigint) (dsz: bigint) (mem: ram) (addr: bigint) (v: bitvector): unit =
    let rec write (i: int): unit =
        if i < (Z.to_int dsz) then
            let b = char_of_int (Z.to_int (Z.extract v.v (i*8) 8)) in
            writeByte_ram mem (Z.add addr (Z.of_int i)) b;
            write (i+1)
    in
    write 0


(****************************************************************)
(** {2 File primops}                                            *)
(****************************************************************)

(** These are not part of the official ASL language but they are
    useful when implementing the infrastructure needed in simulators.
 *)

let prim_open_file (name: string) (mode: string): bigint =
    failwith "open_file"

let prim_write_file (fd: bigint) (data: string): unit =
    failwith "write_file"

let prim_getc_file (fd: bigint): bigint =
    failwith "getc_file"

let prim_print_str (data: string): unit =
    Printf.printf "%s" data

let prim_print_char (data: bigint): unit =
    Printf.printf "%c" (char_of_int (Z.to_int data))


(****************************************************************)
(** {2 Trace primops}                                           *)
(****************************************************************)

(** These are not part of the official ASL language but they are
    useful when implementing the infrastructure needed in simulators.
 *)

let prim_trace_memory_read (asz: bigint) (dsz: bigint) (mem: ram) (addr: bigint) (v: bitvector): unit = ()
let prim_trace_memory_write (asz: bigint) (dsz: bigint) (mem: ram) (addr: bigint) (v: bitvector): unit = ()
let prim_trace_event (msg: string): unit = ()


(****************************************************************
 * End
 ****************************************************************)
