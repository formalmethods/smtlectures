SOURCES=$(wildcard demo-*.tex)
TARGETS=$(SOURCES:.tex=-fig)

all: $(TARGETS)

%-fig: %.tex
	@pdflatex --jobname=$@ $?

clean:
	@rm -f *.out *.aux *.log *.nav *.snm *.toc
