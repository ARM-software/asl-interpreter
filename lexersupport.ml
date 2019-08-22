(****************************************************************
 * ASL lexer support
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** ASL lexer support *)

open Lexer
open Lexing
open Asl_parser

let string_of_token (t: Asl_parser.token): string =
    ( match t with
    | AMPERSAND           -> "amp"
    | AMPERSAND_AMPERSAND -> "ampamp"
    | AND                 -> "and"
    | ARRAY               -> "array"
    | ASSERT              -> "assert"
    | BANG                -> "bang"
    | BAR_BAR             -> "barbar"
    | BITS                -> "bits"
    | BITSLIT(x)          -> "bin:"^x
    | UNDERSCORE_UNDERSCORE_ARRAY                           -> "__array"
    | UNDERSCORE_UNDERSCORE_BUILTIN                         -> "__builtin"
    | UNDERSCORE_UNDERSCORE_CONDITIONAL                     -> "__conditional"
    | UNDERSCORE_UNDERSCORE_CONFIG                          -> "__config"
    | UNDERSCORE_UNDERSCORE_DECODE                          -> "__decode"
    | UNDERSCORE_UNDERSCORE_ENCODING                        -> "__encoding"
    | UNDERSCORE_UNDERSCORE_EXCEPTIONTAKEN                  -> "__ExceptionTaken"
    | UNDERSCORE_UNDERSCORE_EXECUTE                         -> "__execute"
    | UNDERSCORE_UNDERSCORE_EVENT                           -> "__event"
    | UNDERSCORE_UNDERSCORE_FIELD                           -> "__field"
    | UNDERSCORE_UNDERSCORE_FUNCTION                        -> "__function"
    | UNDERSCORE_UNDERSCORE_GUARD                           -> "__guard"
    | UNDERSCORE_UNDERSCORE_INSTRUCTION                     -> "__instruction"
    | UNDERSCORE_UNDERSCORE_INSTRUCTION_UNDERSCORE_SET      -> "__instruction_set"
    | UNDERSCORE_UNDERSCORE_MAP                             -> "__map"
    | UNDERSCORE_UNDERSCORE_NOP                             -> "__NOP"
    | UNDERSCORE_UNDERSCORE_NEWEVENT                        -> "__newevent"
    | UNDERSCORE_UNDERSCORE_NEWMAP                          -> "__newmap"
    | UNDERSCORE_UNDERSCORE_OPCODE                          -> "__opcode"
    | UNDERSCORE_UNDERSCORE_OPERATOR_ONE                    -> "__operator1"
    | UNDERSCORE_UNDERSCORE_OPERATOR_TWO                    -> "__operator2"
    | UNDERSCORE_UNDERSCORE_POSTDECODE                      -> "__postdecode"
    | UNDERSCORE_UNDERSCORE_READWRITE                       -> "__readwrite"
    | UNDERSCORE_UNDERSCORE_REGISTER                        -> "__register"
    | UNDERSCORE_UNDERSCORE_UNALLOCATED                     -> "__UNALLOCATED"
    | UNDERSCORE_UNDERSCORE_UNPREDICTABLE_UNDERSCORE_UNLESS -> "__unpredictable_unless"
    | UNDERSCORE_UNDERSCORE_UNPREDICTABLE                   -> "__UNPREDICTABLE"
    | UNDERSCORE_UNDERSCORE_WRITE                           -> "__write"
    | CARET               -> "caret"
    | CASE                -> "case"
    | CATCH               -> "catch"
    | COLON               -> "colon"
    | COMMA               -> "comma"
    | CONSTANT            -> "constant"
    | CONSTRAINED_UNDERSCORE_UNPREDICTABLE -> "constrained_unpredictable"
    | DEDENT              -> "dedent"
    | DIV                 -> "div"
    | DO                  -> "do"
    | DOT                 -> "dot"
    | DOT_DOT             -> "dotdot"
    | DOWNTO              -> "downto"
    | ELSE                -> "else"
    | ELSIF               -> "elsif"
    | ENUMERATION         -> "enum"
    | EOF                 -> "eof"
    | EOL1                -> "eol"
    | EOL2 ()             -> "eol"
    | EOR                 -> "eor"
    | EQ                  -> "eq"
    | EQ_EQ               -> "eqeq"
    | EQ_GT               -> "eqgt"
    | REALLIT(x)          -> "real:"^x
    | FOR                 -> "for"
    | GT                  -> "gt"
    | GT_EQ               -> "gteq"
    | GT_GT               -> "gtgt"
    | HEXLIT(x)           -> "hex:"^x
    | ID(x)               -> "ident:"^x
    | IF                  -> "if"
    | IMPLEMENTATION_UNDERSCORE_DEFINED -> "impdef"
    | IN                  -> "in"
    | IFF                 -> "iff"
    | IMPLIES             -> "implies"
    | INDENT              -> "indent"
    | INTLIT(x)           -> "int:" ^ x
    | IS                  -> "is"
    | LBRACE              -> "lbrace"
    | LBRACE_LBRACE       -> "{{"
    | LBRACK              -> "lbrack"
    | LPAREN              -> "lparen"
    | LT                  -> "lt"
    | LT_EQ               -> "lteq"
    | LT_LT               -> "ltlt"
    | MASKLIT(x)          -> "mask:"^x
    | MINUS               -> "minus"
    | MOD                 -> "mod"
    | BANG_EQ             -> "neq"
    | NOT                 -> "not"
    | OF                  -> "of"
    | OR                  -> "or"
    | OTHERWISE           -> "otherwise"
    | PLUS                -> "plus"
    | PLUS_PLUS           -> "plusplus"
    | PLUS_COLON          -> "pluscolon"
    | QUALIFIER(x)        -> "qualifier:"^x
    | QUOT                -> "quot"
    | RBRACE              -> "rbrace"
    | RBRACE_RBRACE       -> "}}"
    | RBRACK              -> "rbrack"
    | RECORD              -> "record"
    | REM                 -> "rem"
    | REPEAT              -> "repeat"
    | RETURN              -> "return"
    | RPAREN              -> "rparen"
    | SEE                 -> "see"
    | SEMICOLON           -> "semi"
    | SLASH               -> "slash"
    | STAR                -> "star"
    | STRINGLIT(x)        -> "string:" ^ x
    | THEN                -> "then"
    | THROW               -> "throw"
    | TYPEID(x)           -> "tident:"^x
    | TO                  -> "to"
    | TRY                 -> "try"
    | TYPE                -> "type"
    | TYPEOF              -> "typeof"
    | UNDEFINED           -> "undefined"
    | UNKNOWN             -> "unknown"
    | UNPREDICTABLE       -> "unpredictable"
    | UNTIL               -> "until"
    | WHEN                -> "when"
    | WHILE               -> "while"
    )

let print_position outx lexbuf =
    let pos = lexbuf.lex_curr_p in
    Printf.fprintf outx "%s:%d:%d" pos.pos_fname
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let starters : Asl_parser.token list = [LPAREN; LBRACK; LBRACE; IF; ELSIF; WHILE]
let enders   : Asl_parser.token list = [RPAREN; RBRACK; RBRACE; THEN; DO]

type offside_state = {
    mutable stack  : int list;          (* indentation history *)
    mutable parens : int;               (* number of outstanding openers *)
    mutable newline: bool;              (* processing newline *)
    mutable next   : Asl_parser.token;  (* next token *)
}

let offside_token (read: Lexing.lexbuf -> Asl_parser.token): (Lexing.lexbuf -> Asl_parser.token) =
    let state = {
        stack   = [0];
        parens  = 0;
        newline = false;
        next    = EOL1
    } in

    let pushStack (col: int): Asl_parser.token = begin
        state.stack <- col :: state.stack;
        INDENT
    end in

    let getToken (buf: Lexing.lexbuf): Asl_parser.token = begin
        let useToken _ : Asl_parser.token = begin
            let tok : Asl_parser.token = state.next in
            if List.mem tok starters then begin
                state.parens <- state.parens + 1
            end else if (state.parens > 0) && (List.mem tok enders) then begin
                state.parens <- state.parens - 1
            end;
            (try
                state.next <- read buf
             with Lexer.Eof -> state.next <- EOF);
            tok
        end in

        if state.parens > 0 then begin
            (* In parentheses: ignore EOL tokens *)
            while state.next = EOL1 do
                ignore (useToken())
            done;
            useToken()
        end else if state.next = EOF then begin
            (* End of file: emit outstanding DEDENT tokens *)
            begin match state.stack with
            | []
            | [_] ->
                    EOF
            | (d::ds) ->
                    state.stack <- ds;
                    DEDENT
            end
        end else if state.next = EOL1  then begin
            while state.next = EOL1 do
                state.newline <- true;
                ignore(useToken())
            done;
            EOL1
        end else begin
            if state.newline then begin
                let prev_col = List.hd state.stack in
                let pos = lexeme_start_p buf in
                let new_column = pos.pos_cnum - pos.pos_bol in
                if new_column > prev_col then begin
                    state.newline <- false;
                    pushStack new_column
                end else if new_column = prev_col then begin
                    state.newline <- false;
                    useToken()
                end else begin
                    state.stack <- List.tl state.stack;
                    let target_column = List.hd state.stack in
                    (* state.newline <- false; *)
                    state.newline <- new_column <> target_column;
                    (* This gives spurious warnings when indentation is
                     * decremented in two steps.
                     *
                     * if new_column < target_column then begin
                     *     Printf.printf "Warning: incorrect indentation %d: %d %d\n"
                     *         buf.lex_curr_p.pos_lnum
                     *         new_column target_column
                     * end;
                     *)
                    DEDENT
                end
            end else begin
                useToken()
            end
        end
    end
    in
    getToken

(****************************************************************
 * End
 ****************************************************************)
