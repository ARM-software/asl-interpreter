////////////////////////////////////////////////////////////////
// ASL standard prelude
//
// Copyright Arm Limited (c) 2017-2019
// SPDX-Licence-Identifier: BSD-3-Clause
////////////////////////////////////////////////////////////////

__builtin type integer;
__builtin type real;
__builtin type string;
__builtin type __mask; // todo: should have a type parameter
__builtin type __Exception;
__builtin type __RAM; // todo: should have a type parameter

type bit = bits(1);

enumeration boolean { FALSE, TRUE };
enumeration signal { LOW, HIGH };

__builtin boolean   eq_bool(boolean x, boolean y);
__builtin boolean   ne_bool(boolean x, boolean y);
__builtin boolean   not_bool(boolean x);
__builtin boolean   and_bool(boolean x, boolean y);
__builtin boolean   or_bool(boolean x, boolean y);
__builtin boolean   equiv_bool(boolean x, boolean y);
__builtin boolean   implies_bool(boolean x, boolean y);

__builtin boolean   eq_int(integer x, integer y);
__builtin boolean   ne_int(integer x, integer y);
__builtin boolean   gt_int(integer x, integer y);
__builtin boolean   ge_int(integer x, integer y);
__builtin boolean   le_int(integer x, integer y);
__builtin boolean   lt_int(integer x, integer y);
__builtin boolean   is_pow2_int(integer x);
__builtin integer   add_int(integer x, integer y);
__builtin integer   neg_int(integer x);
__builtin integer   sub_int(integer x, integer y);
__builtin integer   shl_int(integer x, integer y);
__builtin integer   shr_int(integer x, integer y);
__builtin integer   mul_int(integer x, integer y);
__builtin integer   zdiv_int(integer x, integer y);
__builtin integer   zrem_int(integer x, integer y);
__builtin integer   fdiv_int(integer x, integer y);
__builtin integer   frem_int(integer x, integer y);
__builtin integer   mod_pow2_int(integer x, integer y);
__builtin integer   align_int(integer x, integer y);
__builtin integer   pow2_int(integer y);

__builtin real      cvt_int_real(integer x);
__builtin boolean   eq_real(real x, real y);
__builtin boolean   ne_real(real x, real y);
__builtin boolean   le_real(real x, real y);
__builtin boolean   lt_real(real x, real y);
__builtin boolean   gt_real(real x, real y);
__builtin boolean   ge_real(real x, real y);
__builtin real      add_real(real x,    real y);
__builtin real      neg_real(real x);
__builtin real      sub_real(real x, real y);
__builtin real      mul_real(real x, real y);
__builtin real      divide_real(real x, real y);
__builtin real      pow2_real(integer y);
__builtin integer   round_tozero_real(real x);
__builtin integer   round_down_real(real x);
__builtin integer   round_up_real(real x);
__builtin real      sqrt_real(real x);

__builtin bits(N)   cvt_int_bits(integer x, integer N);
__builtin integer   cvt_bits_sint(bits(N) x);
__builtin integer   cvt_bits_uint(bits(N) x);
__builtin boolean   in_mask(bits(N) x, __mask(N) y);
__builtin boolean   notin_mask(bits(N) x, __mask(N) y);
__builtin boolean   eq_bits(bits(N) x, bits(N) y);
__builtin boolean   ne_bits(bits(N) x, bits(N) y);
__builtin bits(N)   add_bits(bits(N) x, bits(N) y);
__builtin bits(N)   sub_bits(bits(N) x, bits(N) y);
__builtin bits(N)   mul_bits(bits(N) x, bits(N) y);
__builtin integer   frem_bits_int(bits(N) x, integer y);
__builtin bits(N)   and_bits(bits(N) x, bits(N) y);
__builtin bits(N)   or_bits(bits(N) x, bits(N) y);
__builtin bits(N)   eor_bits(bits(N) x, bits(N) y);
__builtin bits(N)   not_bits(bits(N) x);
__builtin bits(N)   zeros_bits();
__builtin bits(N)   ones_bits();

bits(N) add_bits_int(bits(N) x, integer y)
    return add_bits(x, cvt_int_bits(y, N));

bits(N) sub_bits_int(bits(N) x, integer y)
    return sub_bits(x, cvt_int_bits(y, N));

__operator2 + = add_int, add_real, add_bits, add_bits_int;
__operator2 - = sub_int, sub_real, sub_bits, sub_bits_int;
__operator1 - = neg_int, neg_real;
__operator2 * = mul_int, mul_real, mul_bits;
__operator2 / = divide_real;

__builtin bits(M*N) replicate_bits(bits(M) x, integer N);
__builtin bits(M+N) append_bits(bits(M) x, bits(N) y);

__builtin boolean   is_cunpred_exc(__Exception ex);
__builtin boolean   is_exctaken_exc(__Exception ex);
__builtin boolean   is_impdef_exc(__Exception ex);
__builtin boolean   is_see_exc(__Exception ex);
__builtin boolean   is_undefined_exc(__Exception ex);
__builtin boolean   is_unpred_exc(__Exception ex);

__builtin string    cvt_int_hexstr(integer x);
__builtin string    cvt_int_decstr(integer x);
__builtin string    cvt_bool_str(boolean x);
__builtin string    cvt_bits_str(integer N, bits(N) x);
__builtin string    cvt_real_str(real x);
__builtin string    append_str_str(string x, string y);
__builtin boolean   eq_str(string x, string y);
__builtin boolean   ne_str(string x, string y);
__builtin ()        print_str(string x);
__builtin ()        print_char(integer x);

__builtin ()        asl_pragma(string x);

__builtin integer   asl_file_open(string name, string mode);
__builtin integer   asl_file_write(integer fd, string data);
__builtin integer   asl_file_getc(integer fd);

__builtin ()        ram_init(integer A, integer N, __RAM(A) ram, bits(8*N) val);
__builtin bits(8*N) ram_read(integer A, integer N, __RAM(A) ram, bits(A) address);
__builtin ()        ram_write(integer A, integer N, __RAM(A) ram, bits(A) address, bits(8*N) val);

__InitRAM(integer A, integer N, __RAM(A) ram, bits(8*N) val)
    ram_init(A, N, ram, val);

bits(8*N) __ReadRAM(integer A, integer N, __RAM(A) ram, bits(A) address)
    return ram_read(A, N, ram, address);

__WriteRAM(integer A, integer N, __RAM(A) ram, bits(A) address, bits(8*N) val)
    ram_write(A, N, ram, address, val);

__builtin ()        trace_memory_write(integer N, bits(A) address, bits(8*N) val);
__builtin ()        trace_memory_read(integer N, bits(A) address, bits(8*N) val);
__builtin ()        trace_event(string event);

__tarmacEvent(string event)
    trace_event(event);

__builtin ()        sleep_request();
__builtin ()        wakeup_request();
__builtin ()        program_end();

__builtin ()        decodeInstr_A64(bits(32) instr);
__builtin ()        decodeInstr_A32(bits(32) instr);
__builtin ()        decodeInstr_T32(bits(32) instr);
__builtin ()        decodeInstr_T16(bits(16) instr);

print(bits(N) x)
    print_str(cvt_bits_str(N, x));

print(string x)
    print_str(x);

println()
    print_char(10);

println(string x)
    print_str(x);
    print_char(10);

putchar(integer c)
    print_char(c);

__abort()
    program_end();

__operator1 !       = not_bool;
__operator2 &&      = and_bool;
__operator2 ||      = or_bool;
__operator2 IFF     = equiv_bool;
__operator2 IMPLIES = implies_bool;

// omit since they are auto-generated
// __operator2 == = eq_bool;
// __operator2 != = ne_bool;

__operator2 == = eq_int, eq_real, eq_bits, eq_str, in_mask;
__operator2 != = ne_int, ne_real, ne_bits, ne_str, notin_mask;
__operator2 <= = le_int, le_real;
__operator2 >= = ge_int, ge_real;
__operator2 <  = lt_int, lt_real;
__operator2 >  = gt_int, gt_real;

integer shift_left_int(integer x, integer y)
    return if y >= 0 then shl_int(x, y) else shr_int(x, -y);

integer shift_right_int(integer x, integer y)
    return if y >= 0 then shr_int(x, y) else shl_int(x, -y);

__operator2 << = shift_left_int;
__operator2 >> = shift_right_int;

integer pow_int_int(integer x, integer y)
    if x == 2 then
        return pow2_int(y); // optimized case
    else
        assert y >= 0;
        integer result = 1;
        for i = 1 to y
            result = result * x;
        return result;

real pow_real_int(real x, integer y)
    assert x == 2.0;
    return pow2_real(y);

__operator2 ^ = pow_int_int, pow_real_int;

real Real(integer x)
    return cvt_int_real(x);

integer frem_bits_int(bits(N) x, integer y)
    assert y > 0;
    return frem_int(cvt_bits_uint(x), y);

// Division: round to zero
__operator2 QUOT = zdiv_int;
__operator2 REM  = zrem_int;

// Division: round to -infinity (floor)
__operator2 DIV  = fdiv_int;
__operator2 MOD  = frem_int, frem_bits_int;

__operator2 AND  = and_bits;
__operator2 OR   = or_bits;
__operator2 EOR  = eor_bits;
__operator1 NOT  = not_bits;

string HexStr(integer x)
    return cvt_int_hexstr(x);

string DecStr(integer x)
    return cvt_int_decstr(x);

string append_str_bool(string x, boolean y)
    return append_str_str(x, cvt_bool_str(y));

string append_bool_str(boolean x, string  y)
    return append_str_str(cvt_bool_str(x), y);

string append_str_bits(string  x, bits(N) y)
    return append_str_str(x, cvt_bits_str(N, y));

string append_bits_str(bits(N) x, string  y)
    return append_str_str(cvt_bits_str(N, x), y);

string append_str_real(string  x, real y)
    return append_str_str(x, cvt_real_str(y));

string append_real_str(real x, string  y)
    return append_str_str(cvt_real_str(x), y);

string append_str_int(string  x, integer y)
    return append_str_str(x, DecStr(y));

string append_int_str(integer x, string  y)
    return append_str_str(DecStr(x), y);

__operator2 ++ = append_str_str;
__operator2 ++ = append_str_bool, append_bool_str;
__operator2 ++ = append_str_real, append_real_str;
__operator2 ++ = append_str_bits, append_bits_str;
__operator2 ++ = append_str_int,  append_int_str;

__operator2 : = append_bits;

bits(M*N) Replicate(bits(M) x, integer N)
    return replicate_bits(x, N);

bits(N) Replicate(bits(M) x)
    assert N MOD M == 0;
    return replicate_bits(x, N DIV M);

bits(N) Zeros(integer N)
    return zeros_bits();

bits(N) Ones(integer N)
    return ones_bits();

bits(N) Zeros()
    return zeros_bits();

bits(N) Ones()
    return ones_bits();

boolean IsOnes(bits(N) x)
    return x == Ones();

boolean IsZero(bits(N) x)
    return x == Zeros();

bits(N) SignExtend(bits(M) x, integer N)
    assert N >= M;
    return Replicate(x[M-1], N-M) : x;

bits(N) ZeroExtend(bits(M) x, integer N)
    assert N >= M;
    return Zeros(N-M) : x;

// The existence of SignExtend and ZeroExtend makes the
// typesystem considerably more complex because we cannot
// determine the value of 'N' just from the types of the
// arguments.
bits(N) SignExtend(bits(M) x)
    return SignExtend(x, N);

bits(N) ZeroExtend(bits(M) x)
    return ZeroExtend(x, N);

real Sqrt(real x)
    return sqrt_real(x);

integer RoundTowardsZero(real x)
    return round_tozero_real(x);

integer RoundDown(real x)
    return round_down_real(x);

integer RoundUp(real x)
    return round_up_real(x);

boolean IsUNDEFINED(__Exception x)
    return is_undefined_exc(x);

boolean IsUNPREDICTABLE(__Exception x)
    return is_unpred_exc(x);

boolean IsSEE(__Exception x)
    return is_see_exc(x);

boolean IsExceptionTaken(__Exception x)
    return is_exctaken_exc(x);

integer UInt(integer N, bits(N) x)
    return cvt_bits_uint(x);

integer UInt(bits(N) x)
    return cvt_bits_uint(x);

integer SInt(integer N, bits(N) x)
    return cvt_bits_sint(x);

integer SInt(bits(N) x)
    return cvt_bits_sint(x);

bits(N) Align(bits(N) x, integer y)
    return align_int(cvt_bits_uint(x), y)[N-1:0];

integer Align(integer x, integer y)
    return align_int(x, y);


////////////////////////////////////////////////////////////////
// End
////////////////////////////////////////////////////////////////
