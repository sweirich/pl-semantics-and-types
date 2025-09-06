Source files for Lecture Notes PDF
-----------------------------------

To typeset these notes, you will need to have installed LaTeX and the Ott
tool. The easiest way to install Ott is through
[opam](https://opam.ocaml.org/).

The Ott tool assists with typesetting mathematical specifications of type
systems. All typing rules that appear in the lecture notes are specified
within the following source files.

[Ott](https://www.cl.cam.ac.uk/~pes20/ott/top2.html) specifications:
+ [stlc.ott](ott/stlc.ott) - Simply-Typed Lambda Calculus

The OTT tool processes the ott file(s) into a set of LaTeX definitions. If there
are multiple ott files specified, they are merged into a single file. Even 
though this file is generated, we include it here in case you have trouble 
installing Ott.
+ [all-rules.tex](all-rules.tex) 

The OTT tool also process the source files for the notes, expanding the 
and parts of the file in `[[..]]' into the appropriate LaTeX macro calls. 
By convention, we use the `.mng` extension for these files. 

LaTeX source files
+ [plst.mng](plst.mng) - Toplevel file the notes document
+ [stlc.mng](stlc.mng) - Chapter: Simply-Typed Lambda Calclus
+ [nrec.mng](nrec.mng) - Chapter: Natural Number Recursion

For each file above, Ott produces a `.tex` file, which is then processed 
by LaTeX. Again, this repository includes these generated files in case 
you have trouble installing Ott.

Other files
+ [ottalt.sty](ottalt.sty) - [Auxiliary style file](https://users.cs.northwestern.edu/~jesse/code/latex/ottalt/ottalt.pdf) for working with Ott produced LaTeX macros
+ [listproc.sty](listproc.sty) - Auxiliary style file for ottall.sty
+ [Makefile](Makefile) - build the notes 
