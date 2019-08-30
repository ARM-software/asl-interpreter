(****************************************************************
 * ASL interactive frontend
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** ASL interactive frontend *)

open Asl_ast

module Lexer  = Lexer
module Parser = Asl_parser
module TC     = Tcheck
module PP     = Asl_parser_pp
module AST    = Asl_ast

open Lexersupport
open Lexing

let opt_filenames : string list ref = ref []
let opt_print_version = ref false
let opt_verbose       = ref false

let read_file (filename : string) (isPrelude: bool): AST.declaration list =
    if !opt_verbose then Printf.printf "Processing %s\n" filename;
    let inchan = open_in filename in
    let lexbuf = Lexing.from_channel inchan in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
    let t =
        (try
            (* Apply offside rule to raw token stream *)
            let lexer = offside_token Lexer.token in

            (* Run the parser on this line of input. *)
            if !opt_verbose then Printf.printf "- Parsing %s\n" filename;
            Parser.declarations_start lexer lexbuf
        with
        | Parse_error_locn(l, s) -> begin
            Printf.printf "  Syntax error %s at %s\n" s (pp_loc l);
            exit 1
        end
        | PrecedenceError(loc, op1, op2) -> begin
            Printf.printf "  Syntax error: operators %s and %s require parentheses to disambiguate expression at location %s\n"
                (Utils.to_string (Asl_parser_pp.pp_binop op1))
                (Utils.to_string (Asl_parser_pp.pp_binop op2))
                (pp_loc loc);
            exit 1
        end
        | Parser.Error -> begin
            let curr = lexbuf.Lexing.lex_curr_p in
            let tok = Lexing.lexeme lexbuf in
            Printf.printf "  Parser error at %s '%s'\n" (AST.pp_lexing_position curr) tok;
            exit 1
        end
        )
    in
    close_in inchan;

    if false then PPrint.ToChannel.pretty 1.0 60 stdout (PP.pp_declarations t);
    if !opt_verbose then Printf.printf "  - Got %d declarations from %s\n" (List.length t) filename;

    let t' =
        try
            if !opt_verbose then Printf.printf "- Typechecking %s\n" filename;
            let t' = TC.tc_declarations isPrelude t in
            t'
        with
        | TC.UnknownObject (loc, what, x) ->
            Printf.printf "  %s: Type error: Unknown %s %s\n" (pp_loc loc) what x;
            exit 1
        | TC.DoesNotMatch (loc, what, x, y) ->
            Printf.printf "  %s: Type error: %s %s does not match %s\n" (pp_loc loc) what x y;
            exit 1
        | TC.IsNotA (loc, what, x) ->
            Printf.printf "  %s: Type error: %s is not a %s\n" (pp_loc loc) x what;
            exit 1
        | TC.Ambiguous (loc, what, x) ->
            Printf.printf "  %s: Type error: %s %s is ambiguous\n" (pp_loc loc) what x;
            exit 1
        | TC.TypeError (loc, what) ->
            Printf.printf "  %s: Type error: %s\n" (pp_loc loc) what;
            exit 1
    in

    if false then PPrint.ToChannel.pretty 1.0 60 stdout (PP.pp_declarations t');
    if !opt_verbose then Printf.printf "  - Got %d typechecked declarations from %s\n" (List.length t') filename;

    if !opt_verbose then Printf.printf "Finished %s\n" filename;
    flush stdout;
    t'

let read_spec (filename : string): AST.declaration list =
    let r: AST.declaration list list ref = ref [] in
    let inchan = open_in filename in
    (try
        while true do
            let t = read_file (input_line inchan) false in
            r := t :: !r
        done
    with
    | End_of_file ->
        close_in inchan
    );
    List.concat (List.rev !r)

let help_msg = [
    {|:? :help                       Show this help message|};
    {|:opcode <instr-set> <int>      Decode and execute opcode|};
    {|:project <file>                Execute ASLi commands in <file>|};
    {|:q :quit                       Exit the interpreter|};
    {|:set impdef <string> = <expr>  Define implementation defined behavior|};
    {|:set +<flag>                   Set flag|};
    {|:set -<flag>                   Clear flag|};
    {|<expr>                         Execute ASL expression|};
    {|<stmt> ;                       Execute ASL statement|}
]

let flags = [
    ("trace:write", Eval.trace_write);
    ("trace:fun",   Eval.trace_funcall);
    ("trace:prim",  Eval.trace_primop);
    ("trace:instr", Eval.trace_instruction)
]

let mkLoc (fname: string) (input: string): AST.l =
    let len = String.length input in
    let start : Lexing.position = { pos_fname = fname; pos_lnum = 1; pos_bol = 0; pos_cnum = 0 } in
    let finish: Lexing.position = { pos_fname = fname; pos_lnum = 1; pos_bol = 0; pos_cnum = len } in
    AST.Range (start, finish)

let rec process_command (tcenv: TC.Env.t) (env: Eval.Env.t) (fname: string) (input0: string): unit =
    let input = String.trim input0 in
    (match String.split_on_char ' ' input with
    | [""] ->
        ()
    | [":help"] | [":?"] ->
        List.iter print_endline help_msg;
        print_endline "\nFlags:";
        List.iter (fun (nm, v) -> Printf.printf "  %s%s\n" (if !v then "+" else "-") nm) flags
    | [":opcode"; iset; opcode] ->
        (* todo: make this code more robust *)
        let op = Value.VBits (Primops.prim_cvt_int_bits (Z.of_int 32) (Z.of_int (int_of_string opcode))) in
        Printf.printf "Decoding and executing instruction %s %s\n" iset (Value.pp_value op);
        let decoder = Eval.Env.getDecoder env (Ident iset) in
        Eval.eval_decode_case AST.Unknown env decoder op
    | (":set" :: "impdef" :: rest) ->
        let cmd    = String.concat " " rest in
        let loc    = mkLoc fname cmd in
        let lexbuf = Lexing.from_string cmd in
        let lexer  = offside_token Lexer.token in
        let CLI_Impdef (x, e) = Parser.impdef_command_start lexer lexbuf in
        let (s, e') = TC.with_unify tcenv loc (fun u ->
            let (e', _) = TC.tc_expr tcenv u loc e in
            e'
        ) in
        let e'' = TC.unify_subst_e s e' in
        let v = Eval.eval_expr loc env e'' in
        Eval.Env.setImpdef env x v
    | [":set"; flag] when Utils.startswith flag "+" ->
        (match List.assoc_opt (Utils.stringDrop 1 flag) flags with
        | None -> Printf.printf "Unknown flag %s\n" flag;
        | Some f -> f := true
        )
    | [":set"; flag] when Utils.startswith flag "-" ->
        (match List.assoc_opt (Utils.stringDrop 1 flag) flags with
        | None -> Printf.printf "Unknown flag %s\n" flag;
        | Some f -> f := false
        )
    | [":project"; prj] ->
        let inchan = open_in prj in
        (try
            while true do
                process_command tcenv env prj (input_line inchan)
            done
        with
        | End_of_file ->
            close_in inchan
        )
    | [":q"] | [":quit"] ->
        exit 0
    | _ ->
        let loc    = mkLoc fname input in
        let lexbuf = Lexing.from_string input in
        let lexer  = offside_token Lexer.token in
        if ';' = String.get input (String.length input - 1) then begin
            let s = Parser.stmt_command_start lexer lexbuf in
            let s' = TC.tc_stmt tcenv s in
            Eval.eval_stmt env s'
        end else begin
            let e = Parser.expr_command_start lexer lexbuf in
            let (s, e') = TC.with_unify tcenv loc (fun u ->
                let (e', _) = TC.tc_expr tcenv u loc e in
                e'
            ) in
            let e'' = TC.unify_subst_e s e' in
            let v = Eval.eval_expr loc env e'' in
            print_endline (Value.pp_value v)
        end
    )

let try_process_command (tcenv: TC.Env.t) (env: Eval.Env.t) (fname: string) (input: string): unit =
    (try
        process_command tcenv env fname input
    with
    | Parse_error_locn(l, s) -> begin
        Printf.printf "  Syntax error %s at %s\n" s (pp_loc l)
    end
    | PrecedenceError(loc, op1, op2) -> begin
        Printf.printf "  Syntax error: operators %s and %s require parentheses to disambiguate expression at location %s\n"
            (Utils.to_string (Asl_parser_pp.pp_binop op1))
            (Utils.to_string (Asl_parser_pp.pp_binop op2))
            (pp_loc loc)
    end
    | Parser.Error ->
        Printf.printf "  Parser error\n";
    | TC.UnknownObject (loc, what, x) ->
        Printf.printf "  %s: Type error: Unknown %s %s\n" (pp_loc loc) what x
    | TC.DoesNotMatch (loc, what, x, y) ->
        Printf.printf "  %s: Type error: %s %s does not match %s\n" (pp_loc loc) what x y
    | TC.IsNotA (loc, what, x) ->
        Printf.printf "  %s: Type error: %s is not a %s\n" (pp_loc loc) x what
    | TC.Ambiguous (loc, what, x) ->
        Printf.printf "  %s: Type error: %s %s is ambiguous\n" (pp_loc loc) what x
    | TC.TypeError (loc, what) ->
        Printf.printf "  %s: Type error: %s\n" (pp_loc loc) what
    | Value.EvalError (loc, msg) ->
        Printf.printf "  %s: Evaluation error: %s\n" (pp_loc loc) msg
    | exc ->
        Printf.printf "  Error %s\n" (Printexc.to_string exc);
        Printexc.print_backtrace stdout
    )

let rec repl (tcenv: TC.Env.t) (env: Eval.Env.t): unit =
    flush stdout;
    (match LNoise.linenoise "ASLi> " with
    | None -> ()
    | Some input ->
        LNoise.history_add input |> ignore;
        try_process_command tcenv env "<stdin>" input;
        repl tcenv env
    )

let options = Arg.align ([
    ( "-v", Arg.Set opt_verbose,              "       Verbose output");
    ( "--version", Arg.Set opt_print_version, "       Print version");
] )

let version = "ASL 0.0 alpha"

let banner = [
    {|            _____  _       _    ___________________________________|};
    {|    /\     / ____|| |     (_)   ASL interpreter                    |};
    {|   /  \   | (___  | |      _    Copyright Arm Limited (c) 2017-2019|};
    {|  / /\ \   \___ \ | |     | |                                      |};
    {| / ____ \  ____) || |____ | |   |} ^ version;
    {|/_/    \_\|_____/ |______||_|   ___________________________________|}
]
let usage_msg =
    ( version
    ^ "\nusage: asl <options> <file1> ... <fileN>\n"
    )

let _ =
  Arg.parse options
    (fun s -> opt_filenames := (!opt_filenames) @ [s])
    usage_msg

let main () =
    if !opt_print_version then Printf.printf "%s\n" version
    else begin
        List.iter print_endline banner;
        print_endline "\nType :? for help";
        let t  = read_file "prelude.asl" true in
        let ts = List.map (fun filename ->
            if Utils.endswith filename ".spec" then begin
                read_spec filename
            end else if Utils.endswith filename ".asl" then begin
                read_file filename false
            end else begin
                failwith ("Unrecognized file suffix on "^filename)
            end
        ) !opt_filenames
        in

        if !opt_verbose then Printf.printf "Building evaluation environment\n";
        let env = (try
            Eval.build_evaluation_environment (List.concat (t::ts))
        with
        | Value.EvalError (loc, msg) ->
            Printf.printf "  %s: Evaluation error: %s\n" (pp_loc loc) msg;
            exit 1
        ) in
        if !opt_verbose then Printf.printf "Built evaluation environment\n";

        LNoise.history_load ~filename:"asl_history" |> ignore;
        LNoise.history_set ~max_length:100 |> ignore;
        repl (TC.Env.mkEnv TC.env0) env
    end

let _ =ignore(main ())

(****************************************************************
 * End
 ****************************************************************)
