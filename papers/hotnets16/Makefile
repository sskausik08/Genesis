FILE=paper

all:
	latex $(FILE)
	bibtex $(FILE)
	latex $(FILE)
	latex $(FILE)
	dvips $(FILE).dvi
	ps2pdf $(FILE).ps
small:
	latex $(FILE)
	dvips $(FILE).dvi
	ps2pdf $(FILE).ps	

view:
	open -a Skim $(FILE).pdf