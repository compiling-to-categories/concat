
%.pdf: %.dot Makefile
	dot -Tpdf -Gmargin=0 -Gsize=10,10 $< -o $@

%.svg: %.dot Makefile
	dot -Tsvg $< -o $@

%.png: %.dot
	dot -Gdpi=200 -Tpng $< -o $@

%.see: %
	open $<

FigSuperDir=/Users/conal/Journals/Current/wikidata/2016/Figures
FigDir=$(FigSuperDir)/$(shell date "+%m-%d")

$(FigDir):
	mkdir $@

$(FigDir)/%.svg: %.dot Makefile $(FigDir)
	dot -Tsvg $< -o $@

%.fig: $(FigDir)/%.svg
	@

.PRECIOUS: %.pdf $(FigDir)/%.svg

