PAPER=portable-warrant
all: $(PAPER).pdf
$(PAPER).pdf: $(PAPER).tex tables/porting-matrix.tex appendices/A-fiber-counterexamples.tex appendices/B-evidence-chain.tex appendices/C-portable-kernel.tex appendices/D-conformance-results.tex appendices/E-warrant-algebra.tex appendices/F-neuroformal-case.tex
	pdflatex -interaction=nonstopmode $(PAPER).tex
	pdflatex -interaction=nonstopmode $(PAPER).tex
clean:
	rm -f *.aux *.log *.out *.toc
verify:
	sha256sum -c artifacts/manifest.sha256
