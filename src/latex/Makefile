all : act.pdf

act.pdf : act.tex
	pdflatex act.tex

clean :
	-rm act.pdf act.aux act.log

cleanall : clean
	-rm Makefile act.tex
