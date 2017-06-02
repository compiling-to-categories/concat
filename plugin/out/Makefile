
%.pdf: %.dot Makefile
	dot -Tpdf -Gmargin=0 -Gsize=10,10 $< -o $@

# Remove page dimensions to make the results self-scaling
%.svg: %.dot # Makefile
	dot -Tsvg $< | sed -e 's/<svg width.*/<svg/'> $@

%.png: %.dot
	dot -Gdpi=200 -Tpng $< -o $@

%.see: %
	open $<

FigSuperDir=/Users/conal/Journals/Current/wikidata/$(shell date "+%Y")/Figures
FigDir=$(FigSuperDir)/$(shell date "+%m-%d")

$(FigDir):
	mkdir -p $@

$(FigDir)/%.svg: %.dot Makefile $(FigDir)
	dot -Tsvg $< | sed -e 's/<svg width.*/<svg/'> $@

%.fig: $(FigDir)/%.svg
	@

.PRECIOUS: %.pdf $(FigDir)/%.svg

