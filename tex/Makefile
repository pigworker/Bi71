default : TypesNi.pdf

TypesNi.tex : TypesNi.lagda
	lhs2Tex --agda TypesNi.lagda > TypesNi.tex

TypesNi.aux : TypesNi.tex
	latex TypesNi

TypesNi.blg : TypesNi.aux TypesNi.bib
	bibtex TypesNi

TypesNi.pdf : TypesNi.tex TypesNi.blg
	pdflatex TypesNi
