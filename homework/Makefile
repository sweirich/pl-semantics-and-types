OTT_SOURCE = ../notes/ott/stlc ott/hw1 ott/hw2 ../notes/ott/bigstep
BIBFILES = 

OTTFILES  = $(foreach i, $(OTT_SOURCE), $(i).ott)
OTTIFLAGS = $(foreach i, $(OTT_SOURCE), -i $(i).ott) -merge true
RULESFILE = all-rules.tex

PAPER_MNG = $(wildcard *.mng)
PAPER_SOURCE = $(patsubst %.mng,%.tex,$(PAPER_MNG))
OTT_FILTER := $(subst .mng,.mng ,$(addprefix -tex_filter ,$(join $(PAPER_MNG), $(PAPER_SOURCE))))

TOP=hw2

all: $(TOP).pdf

%.tex : $(RULESFILE) %.mng Makefile
	rm -f $(PAPER_SOURCE)
	ott -tex_wrap false \
            -tex_show_meta false \
            $(OTTIFLAGS) \
            $(OTT_FILTER)
	chmod a-w $(PAPER_SOURCE)

$(RULESFILE): $(OTTFILES)
	ott $(OTTIFLAGS) -o $(RULESFILE) \
          -tex_wrap false \
          -tex_show_meta false

$(TOP).pdf : $(TOP).tex  $(BIBFILES) $(PAPER_SOURCE) Makefile 
	latexmk -pdflatex="texfot pdflatex" -bibtex -pdf $(TOP).tex -synctex=1 && latexmk -c

deps:
	echo $(PAPER_SOURCE)

paperclean:
	rm -if *-rules.tex $(TOP).tex *.log ./*~  *.aux $(PDFS) *.bbl *.blg *.fdb_latexmk *.fls *.out *-input.tex *~ *.synctex.gz


clean: paperclean
