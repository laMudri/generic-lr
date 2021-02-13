.PHONY: clean default

default: tex/notes/notes.pdf

lagda_files != grep -oh 'src/latex/.*.tex' tex/notes/notes.tex |tr '\n' ' '

src/latex/%.tex: src/%.lagda.tex
	cd src && agda --latex $(shell echo $< |tail -c +5)

tex/notes/notes.pdf: tex/notes/notes.tex $(lagda_files)
	latexmk -pdf -halt-on-error -use-make $<

clean:
	latexmk -C
