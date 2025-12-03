COQMAKEFILE=rocq makefile
LIBNAME=plst
SYNTAX=$(wildcard */syntax.sig) $(wildcard */typesyntax.sig)
SYNTAXV = $(SYNTAX:.sig=.v)
LANGS=stlc rec div modal control untyped
SOURCEV = $(addsuffix /*.v,$(LANGS))

COQDOCJS_DIR ?= coqdocjs
EXTRA_DIR = $(COQDOCJS_DIR)/extra
COQDOCFLAGS ?= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE_NAME ?= CoqSrc.mk
COQDOCJS_LN ?= false


.PHONY: rocq syntax clean fullclean coqdoc

all: rocq

# compile all .v files in _CoqProject
rocq: CoqSrc.mk $(SOURCEV)
	make -f CoqSrc.mk

CoqSrc.mk: _CoqProject
	 $(COQMAKEFILE) -arg '-w -variable-collision,-meta-collision,-require-in-module,-notation-overridden' -f _CoqProject -o CoqSrc.mk

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


coqdoc: $(COQMAKEFILE_NAME)
	$(MAKE) -f $^ html
ifeq ($(COQDOCJS_LN),true)
	ln -sf ../$(EXTRA_DIR)/resources html
else
	cp -R $(EXTRA_DIR)/resources html
endif

