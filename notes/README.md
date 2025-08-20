Source files for Lecture Notes, PDF
-----------------------------------

To typeset these notes, you will need to have installed LaTeX and the Ott
tool. The easiest way to install Ott is through
[opam](https://opam.ocaml.org/).

The Ott tool assists with typesetting mathematical specifications of type
systems. All typing rules that appear in the lecture notes are specified
within the following source files.

[Ott](https://www.cl.cam.ac.uk/~pes20/ott/top2.html) specifications:
+ [stlc.ott](ott/stlc.ott) - Simply-Typed Lambda Calculus

LaTeX source files
+ [oplss.mng](oplss.mng) - Main text of the document
+ [lstpi.sty](lstpi.sty) - [Listings](https://ctan.mirrors.hoobly.com/macros/latex/contrib/listings/listings.pdf) specification for  typesetting `pi-forall` source code
+ [ottalt.sty](ottalt.sty) - [Auxiliary style file](https://users.cs.northwestern.edu/~jesse/code/latex/ottalt/ottalt.pdf) for working with Ott produced LaTeX macros
+ Makefile - how to put everything together
