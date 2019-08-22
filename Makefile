################################################################
# ASL Makefile
#
# Copyright Arm Limited (c) 2017-2019
# SPDX-Licence-Identifier: BSD-3-Clause
################################################################

.DEFAULT: all

OTT             := ott

BUILDFLAGS      += -use-ocamlfind
BUILDFLAGS      += -tag thread
BUILDFLAGS      += -tag debug
BUILDFLAGS      += -cflags -safe-string

MENHIR_EXTRA    = `opam config var ott:share`/menhir_library_extra.mly
MENHIRFLAGS     += --infer
MENHIRFLAGS     += --explain
MENHIR          := -menhir "menhir $(MENHIRFLAGS)"


SRCS += asl_ast.ml
SRCS += asl_parser.mly
SRCS += asl_parser_pp.ml
SRCS += asli.ml
SRCS += lexersupport.ml
SRCS += lexer.mll
SRCS += tcheck.ml
SRCS += asl_utils.ml
SRCS += asl_visitor.ml
SRCS += utils.ml
SRCS += visitor.ml
SRCS += primops.ml
SRCS += value.ml
SRCS += eval.ml

all :: asli.native
asli.native: $(SRCS)
	echo Execute the following: export DYLD_LIBRARY_PATH=`opam config var z3:lib`
	ocamlbuild $(BUILDFLAGS) $(MENHIR) $@

asli.byte: $(SRCS)
	echo Execute the following: export DYLD_LIBRARY_PATH=`opam config var z3:lib`
	ocamlbuild $(BUILDFLAGS) $(MENHIR) $@

doc :: asli.docdir/index.html
asli.docdir/index.html: $(SRCS)
	ocamlbuild -use-ocamlfind $@

all :: asli
asli: asli.native
	ln -f -s $^ asli

clean ::
	$(RM) asli.byte asli.native asli
	$(RM) -r _build
	$(RM) asl.tex asl_ast.ml asl_parser.mly asl_lexer.mll asl_parser_pp.ml
	$(RM) -r asli.docdir
	ocamlbuild -clean

all :: testlexer.native

testlexer.native: testlexer.ml lexersupport.ml lexer.mll asl_parser.mly
	# Adding Z3 to the dynamic library path would not be necessary if we made
	# use of the Z3 package conditional on what target we were building
	echo Execute the following: export DYLD_LIBRARY_PATH=`opam config var z3:lib`
	ocamlbuild $(BUILDFLAGS) $(MENHIR) $@


# generate the ocaml AST type, ocamllex lexer, menhir parser, and ocaml pretty printers for the AST, all from the Ott soruce
asl_ast.ml  asl_lexer.mll asl_parser.mly asl_parser_pp.ml asl_ast.tex : asl.ott
	$(OTT) -aux_style_rules false -tex_wrap true -quotient_rules false -i asl.ott  -o asl_parser.mly -o asl_lexer.mll -o asl_ast.ml -o asl.tex
	grep -v '^%%' $(MENHIR_EXTRA) >> asl_parser.mly

# We need a separate rule to build LaTeX so that it is unquotiented
# (despite the above specifying -quotient_rules false)
asl_grammar.tex: asl.ott
	grep -v spice asl.ott | grep -v '__builtin' | grep -v '__function' | grep -v '__ExceptionTaken' > asl_clean.ott
	$(OTT) -tex_wrap false -quotient_rules false -generate_aux_rules false -aux_style_rules false -i asl_clean.ott -o $@
	perl -p -i -e 's/{\\textsf{S}}/{}/' $@

clean ::
	$(RM) asl_grammar.tex asl_clean.ott

all :: asl_quotiented.pdf
pdf: asl_quotiented.pdf asl_unquotiented.pdf

asl_quotiented.pdf: asl.ott Makefile
	$(OTT) -quotient_rules true -generate_aux_rules false -i asl.ott -o asl_quotiented.tex
	pdflatex asl_quotiented.tex

asl_unquotiented.pdf: asl.ott Makefile
	$(OTT) -quotient_rules false -generate_aux_rules false -aux_style_rules false -i asl.ott -o asl_unquotiented.tex
	pdflatex asl_unquotiented.tex

clean::
	$(RM) *~
	$(RM) asl_quotiented.{tex,pdf}
	$(RM) asl_unquotiented.{tex,pdf}
	$(RM) *.aux *.log *.bbl *.blg *.dvi *.out *.toc

################################################################
# End
################################################################
