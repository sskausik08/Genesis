genesis.pdf : genesis.tex references.bib introduction.tex appendix.tex conclusion.tex tactics.tex synthesis.tex motivation.tex relatedwork.tex evaluation.tex constrainteval.tex surgeryoptimistic.tex policy.tex
	pdflatex -synctex=1 -interaction=nonstopmode genesis.tex
	bibtex genesis
	pdflatex -synctex=1 -interaction=nonstopmode genesis.tex
	pdflatex -synctex=1 -interaction=nonstopmode genesis.tex

clean : 
	rm genesis.pdf
