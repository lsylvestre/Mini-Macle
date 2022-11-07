CAMLC=ocamlc
CAMLLEX=ocamllex
CAMLDEP=ocamldep

EXE=maclec

INCLUDES=-I src



MENHIR=menhir --unused-tokens --unused-precedence-levels --infer --ocamlc "$(CAMLC) -i $(INCLUDES)"

OBJS=src/prelude.cmo\
	src/syntax.cmo\
	src/const.cmo\
	src/macle.cmo\
	src/print_syntax.cmo\
     src/parser.cmo\
     src/lexer.cmo\
     src/typing.cmo\
     \
     src/compile.cmo\
     \
     src/main.cmo
     
     #\
     src/backend/primitives.cmo\
     src/backend/ident.cmo\
     src/backend/err.cmo\
     src/backend/types.cmo\
     src/backend/hsml_types.cmo\
     src/backend/hsml_typing.cmo\
     src/backend/hsml.cmo\
     src/backend/flat_hsml.cmo\
     src/backend/hsml2vhdl.cmo\
     \
	src/backend/make_platform/hsml2cc.cmo\
     src/backend/make_platform/hsml2gluecode.cmo\
     src/backend/make_platform/gen_hw_tcl.cmo\
     src/backend/make_platform/gen_platform_tcl.cmo\
     src/backend/make_platform/gen_bsp_update_tcl.cmo\
     \
     src/backend/compile.cmo


SRCS=`find src -name "*.ml*"`

all: src/parser.cmi $(OBJS)
	$(CAMLC) $(FLAGS) $(INCLUDES) -o $(EXE) $(OBJS)

.SUFFIXES: .mll .mly .ml .mli .cmo .cmi

.ml.cmo:
	$(CAMLC) $(INCLUDES) $(FLAGS) -c $<

.mli.cmi:
	$(CAMLC) $(INCLUDES) $(FLAGS) -c $<

.mly.ml:
	$(MENHIR) $<

.mll.ml:
	$(CAMLLEX) $<

depend:
	$(CAMLDEP) $(INCLUDES) $(SRCS) > .depend
	menhir --depend src/parser.mly >> .depend

include .depend

prepare:  gen
	mkdir -p gen/apps
	mkdir -p gen/bsp
	mkdir -p gen/c
	mkdir -p gen/ml
	mkdir -p gen/rtl/misc
	mkdir -p gen/qsys

clean:
	rm -f `find . -name "*.cmo"`
	rm -f `find . -name "*.cmi"`
	rm -f $(EXE)

clean-cc: clean-gen-cc

clean-gen-cc:
	(cd gen; make clean)

check-cc:
	(cd gen; make check)

run:
	(./$(EXE) $(SRC) -ocaml-backend | ocaml -dsource)

compile:
	./$(EXE) $(SRC)
