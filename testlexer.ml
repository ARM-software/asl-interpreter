(****************************************************************
 * ASL lexer test harness
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** ASL lexer test harness *)

open Asl_ast

module Lexer = Lexer
module Parser = Asl_parser
module TC = Tcheck
module PP = Asl_parser_pp
open Lexersupport
open Lexing

let opt_filenames : string list ref = ref []
let opt_output : string ref = ref "asl.out" (* not used at present *)
let opt_print_version = ref false

let options = Arg.align ([
    ( "-o", Arg.Set_string opt_output, "<file> Set output file" );
    ( "-v", Arg.Set opt_print_version, "       Print version");
] )

let version = "ASL Lexer 0.0"
let usage_msg =
    ( version
    ^ "\nusage: testlexer <options> <file1.asl> ... <fileN.asl>\n"
    )

let _ =
  Arg.parse options
    (fun s -> opt_filenames := (!opt_filenames) @ [s])
    usage_msg

let _ =
    List.iter (fun filename ->
        let inchan = open_in filename in
        let lexbuf = Lexing.from_channel inchan in

        lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };

        (* Apply offside rule to raw token stream *)
        let lexer = offside_token Lexer.token in

        let eof = ref false in
        while not !eof do
            let tok  = lexer lexbuf in
            let curr = lexbuf.Lexing.lex_curr_p in
            let line = curr.Lexing.pos_lnum in
            let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
            Printf.printf "Token line %d column %d: %s\n" line cnum (string_of_token tok);
            eof := tok = EOF
        done;

        Printf.printf "End of file\n"
    ) !opt_filenames

(****************************************************************
 * End
 ****************************************************************)
