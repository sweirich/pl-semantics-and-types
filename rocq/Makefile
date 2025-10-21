COQMAKEFILE=CoqMakefile
LIBNAME=plst
SYNTAX=$(wildcard */syntax.sig) $(wildcard */typesyntax.sig)
SYNTAXV = $(SYNTAX:.sig=.v)
LANGS=stlc rec div modal
SOURCEV = $(addsuffix /*.v,$(LANGS))

.PHONY: rocq syntax clean fullclean

all: rocq

# compile all .v files in _CoqProject
rocq: CoqSrc.mk $(SOURCEV)
	make -f CoqSrc.mk

CoqSrc.mk: _CoqProject
	 coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module,-notation-overridden' -f _CoqProject -o CoqSrc.mk

# Remove compiled files
clean:
	make -f CoqSrc.mk clean

syntax:	$(SYNTAXV)

%/typesyntax.v: %/typesyntax.sig %/import.v Makefile
	autosubst $< -o $@ -f -p $*/import.v -no-static -s rocq

# Generate the syntax.v files with Autosubst 2 and add imports
# This will run Autosubst 2 
%syntax.v: %syntax.sig Makefile
	autosubst $< -o $@ -f -no-static -s rocq



# Generate syntax files and compile all .v files
# This will run Autosubst 2 
fullmake: _CoqProject coq

# Generate syntax.v files and add all .v files to _CoqProject
# This will run Autosubst 2 
_CoqProject : syntax
	{ echo "-R . $(LIBNAME) " ; ls common/*.v $(SOURCEV) ; } > _CoqProject

# Remove compiled files and also remove
# the Autosubst-2-generated syntax.v files and auxiliary make files
# Regenerating syntax.v files will run Autosubst 2
fullclean: clean
	rm -f $(SYNTAXV)
	rm -f .CoqSrc.mk.d CoqSrc CoqSrc.conf CoqSrc.mk CoqSrc.mk.conf
	rm -f _CoqProject

%.vo: %.v CoqSrc.mk
	make -f CoqSrc.mk $*.vo

vos:  CoqSrc.mk
	@make -f CoqSrc.mk vos

%.vos:  %.v CoqSrc.mk
	@make -f CoqSrc.mk $*.vos
