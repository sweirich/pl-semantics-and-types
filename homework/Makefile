TOP=hw6

BIBFILES = 

OTT_NOTES  = stlc bigstep rec eff modal stack control equiv
OTT_HW     = hw1 hw2 hw3 hw4 hw5 hw6
OTT_SOURCE = $(foreach i, $(OTT_NOTES), ../notes/ott/$(i)) $(foreach i, $(OTT_HW), ott/$(i))
OTTFILES  = $(foreach i, $(OTT_SOURCE), $(i).ott)
OTTIFLAGS = $(foreach i, $(OTT_SOURCE), -i $(i).ott) -merge true
RULESFILE = all-rules.tex

all: $(TOP).pdf

%.tex : $(RULESFILE) %.mng Makefile
	rm -f $*.tax
	ott -tex_wrap false \
            -tex_show_meta false \
            $(OTTIFLAGS) \
            -tex_filter $*.mng $*.tex
	chmod a-w $*.tex

$(RULESFILE): $(OTTFILES)
	ott $(OTTIFLAGS) -o $(RULESFILE) \
          -tex_wrap false \
          -tex_show_meta false

%.pdf : %.tex  $(BIBFILES) $(PAPER_SOURCE) Makefile 
	latexmk -pdflatex="texfot pdflatex" -bibtex -pdf $*.tex -synctex=1 && latexmk -c

deps:
	echo $(PAPER_SOURCE)

paperclean:
	rm -if *-rules.tex $(TOP).tex *.log ./*~  *.aux $(PDFS) *.bbl *.blg *.fdb_latexmk *.fls *.out *-input.tex *~ *.synctex.gz


clean: paperclean
