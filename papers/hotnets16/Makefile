FILE=paper

all:
	pdflatex $(FILE)
	bibtex $(FILE)
	pdflatex $(FILE)
	pdflatex $(FILE)
	
small:
	pdflatex $(FILE)		

view:
	open -a Skim $(FILE).pdf