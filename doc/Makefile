.PHONY: all clean

REPORT_NAME = report

all: $(REPORT_NAME).pdf

$(REPORT_NAME).pdf: $(REPORT_NAME).tex
	mkdir -p build
	latexmk -pdf -output-directory=build $<
	cp build/$@ $@

clean:
	rm -rf build
	rm -f $(REPORT_NAME).pdf
