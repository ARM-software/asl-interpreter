(****************************************************************
 * ASL lexer
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

{
open Asl_parser       (* The type token is defined in parser.mli *)
open Asl_ast

exception Eof

let keywords : (string * Asl_parser.token) list = [
    ("AND",                    AND);
    ("CONSTRAINED_UNPREDICTABLE", CONSTRAINED_UNDERSCORE_UNPREDICTABLE);
    ("DIV",                    DIV);
    ("EOR",                    EOR);
    ("IMPLEMENTATION_DEFINED", IMPLEMENTATION_UNDERSCORE_DEFINED);
    ("IN",                     IN);
    ("IFF",                    IFF);
    ("IMPLIES",                IMPLIES);
    ("MOD",                    MOD);
    ("NOT",                    NOT);
    ("OR",                     OR);
    ("QUOT",                   QUOT);
    ("REM",                    REM);
    ("SEE",                    SEE);
    ("UNDEFINED",              UNDEFINED);
    ("UNKNOWN",                UNKNOWN);
    ("UNPREDICTABLE",          UNPREDICTABLE);
    ("__ExceptionTaken",       UNDERSCORE_UNDERSCORE_EXCEPTIONTAKEN);
    ("__NOP",                  UNDERSCORE_UNDERSCORE_NOP);
    ("__UNALLOCATED",          UNDERSCORE_UNDERSCORE_UNALLOCATED);
    ("__UNPREDICTABLE",        UNDERSCORE_UNDERSCORE_UNPREDICTABLE);
    ("__array",                UNDERSCORE_UNDERSCORE_ARRAY);
    ("__builtin",              UNDERSCORE_UNDERSCORE_BUILTIN);
    ("__conditional",          UNDERSCORE_UNDERSCORE_CONDITIONAL);
    ("__config",               UNDERSCORE_UNDERSCORE_CONFIG);
    ("__decode",               UNDERSCORE_UNDERSCORE_DECODE);
    ("__encoding",             UNDERSCORE_UNDERSCORE_ENCODING);
    ("__event",                UNDERSCORE_UNDERSCORE_EVENT);
    ("__execute",              UNDERSCORE_UNDERSCORE_EXECUTE);
    ("__field",                UNDERSCORE_UNDERSCORE_FIELD);
    ("__function",             UNDERSCORE_UNDERSCORE_FUNCTION);
    ("__guard",                UNDERSCORE_UNDERSCORE_GUARD);
    ("__instruction",          UNDERSCORE_UNDERSCORE_INSTRUCTION);
    ("__instruction_set",      UNDERSCORE_UNDERSCORE_INSTRUCTION_UNDERSCORE_SET);
    ("__map",                  UNDERSCORE_UNDERSCORE_MAP);
    ("__newmap",               UNDERSCORE_UNDERSCORE_NEWMAP);
    ("__newevent",             UNDERSCORE_UNDERSCORE_NEWEVENT);
    ("__operator1",            UNDERSCORE_UNDERSCORE_OPERATOR_ONE);
    ("__operator2",            UNDERSCORE_UNDERSCORE_OPERATOR_TWO);
    ("__opcode",               UNDERSCORE_UNDERSCORE_OPCODE);
    ("__postdecode",           UNDERSCORE_UNDERSCORE_POSTDECODE);
    ("__readwrite",            UNDERSCORE_UNDERSCORE_READWRITE);
    ("__register",             UNDERSCORE_UNDERSCORE_REGISTER);
    ("__unpredictable_unless", UNDERSCORE_UNDERSCORE_UNPREDICTABLE_UNDERSCORE_UNLESS);
    ("__write",                UNDERSCORE_UNDERSCORE_WRITE);
    ("array",                  ARRAY);
    ("assert",                 ASSERT);
    ("bits",                   BITS);
    ("case",                   CASE);
    ("catch",                  CATCH);
    ("constant",               CONSTANT);
    ("do",                     DO);
    ("downto",                 DOWNTO);
    ("else",                   ELSE);
    ("elsif",                  ELSIF);
    ("enumeration",            ENUMERATION);
    ("for",                    FOR);
    ("if",                     IF);
    ("is",                     IS);
    ("of",                     OF);
    ("otherwise",              OTHERWISE);
    ("record",                 RECORD);
    ("repeat",                 REPEAT);
    ("return",                 RETURN);
    ("then",                   THEN);
    ("throw",                  THROW);
    ("to",                     TO);
    ("try",                    TRY);
    ("type",                   TYPE);
    ("typeof",                 TYPEOF);
    ("until",                  UNTIL);
    ("when",                   WHEN);
    ("while",                  WHILE);
]

}

rule token = parse
    (* whitespace and comments *)
    | ['\n']                      { Lexing.new_line lexbuf; EOL1 }
    | [' ' '\t']                  { token lexbuf }
    | '/' '/' [^'\n']*            { token lexbuf }
    | '/' '*'                     { comment 1 lexbuf }

    (* numbers, strings and identifiers *)
    | '"' [^'"']* '"'                        as lxm { STRINGLIT(String.sub lxm 1 (String.length lxm - 2)) }
    | '\'' ['0' '1' ' ']* '\''               as lxm { BITSLIT(String.sub lxm 1 (String.length lxm - 2)) }
    | '\'' ['0' '1' 'x' ' ']* '\''           as lxm { MASKLIT(String.sub lxm 1 (String.length lxm - 2)) }
    | '0''x'['0'-'9' 'A' - 'F' 'a'-'f' '_']+ as lxm { HEXLIT(String.sub lxm 2 (String.length lxm - 2)) }
    | ['0'-'9']+ '.' ['0'-'9']+              as lxm { REALLIT(lxm) }
    | ['0'-'9']+                             as lxm { INTLIT(lxm) }
    | ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* as lxm {
           ( match List.assoc_opt lxm keywords with
           | Some x -> x
           | None   -> if isTypeIdent(lxm) then TYPEID(lxm)
                       else if String.equal lxm "AArch32" then QUALIFIER(lxm)
                       else if String.equal lxm "AArch64" then QUALIFIER(lxm)
                       else ID(lxm)
           )
    }

    (* delimiters *)
    | '!'            { BANG       }
    | '!' '='        { BANG_EQ    }
    | '&' '&'        { AMPERSAND_AMPERSAND }
    | '&'            { AMPERSAND  }
    | '('            { LPAREN     }
    | ')'            { RPAREN     }
    | '*'            { STAR       }
    | '+' '+'        { PLUS_PLUS  }
    | '+'            { PLUS       }
    | '+' ':'        { PLUS_COLON }
    | ','            { COMMA      }
    | '-'            { MINUS      }
    | '.'            { DOT        }
    | '.' '.'        { DOT_DOT    }
    | '/'            { SLASH      }
    | ':'            { COLON      }
    | ';'            { SEMICOLON  }
    | '<'            { LT         }
    | '<' '<'        { LT_LT      }
    | '<' '='        { LT_EQ      }
    | '='            { EQ         }
    | '=' '='        { EQ_EQ      }
    | '=' '>'        { EQ_GT      }
    | '>'            { GT         }
    | '>' '='        { GT_EQ      }
    | '>' '>'        { GT_GT      }
    | '['            { LBRACK     }
    | ']'            { RBRACK     }
    | '^'            { CARET      }
    | '{'            { LBRACE     }
    | '{' '{'        { LBRACE_LBRACE }
    | '|' '|'        { BAR_BAR    }
    | '}'            { RBRACE     }
    | '}' '}'        { RBRACE_RBRACE }
    | eof            { raise Eof  }
    | _ as c         { Printf.printf "%s:%d Unrecognized character '%c'\n"
                           lexbuf.lex_curr_p.pos_fname
                           lexbuf.lex_curr_p.pos_lnum
                           c;
                       exit 0 }

and comment depth = parse
      '/' '*' { comment (depth+1) lexbuf }
    | '*' '/' { if depth = 1 then token lexbuf else comment (depth-1) lexbuf }
    | '\n'    { Lexing.new_line lexbuf; comment depth lexbuf }
    | _       { comment depth lexbuf }

(****************************************************************
 * End
 ****************************************************************)
