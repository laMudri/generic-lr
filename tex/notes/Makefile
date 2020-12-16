.PHONY: clean default

default: notes.pdf

lagda_files != grep -oh '../../src/latex/.*.tex' notes.tex |tr '\n' ' '

../../src/latex/%.tex: ../../src/%.lagda.tex
	cd ../../src && agda --latex $(shell echo $< |tail -c +11)

notes.pdf: notes.tex $(lagda_files)
	latexmk -pdf -halt-on-error -use-make $<

clean:
	latexmk -C
