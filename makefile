DOT_FILES = $(shell find ./ -type f -name '*.dot')
DATE=`date +'%d/%m/%y'`

dot:
	@ for b in $(basename $(DOT_FILES)) ; do \
	  dot -T pdf -o $$b.pdf $$b.dot ; \
	done

# End of day commit
# eod:
# 	git add -A ; \
# 	git commit -m "end of day $(DATE)" ; \
# 	git push origin master ; \

# Isabelle snippets
# snippets:
# 	isabelle build -D.; \
# 	sed -n '/\\snip{/,/endsnip/p' output/document/*.tex > snippets-ltl.tex; \

clean:
	@find . -name "*thy~*" -exec rm {} \;

cleanall:
	@find . -name "*thy~*" -exec rm {} \;
	@find . -name "*.dot" -exec rm {} \;
	@find . -name "*.pdf" -exec rm {} \;
	@find . -wholename "*/theories/*.sal" -exec rm {} \;
	@find . -wholename "*/models/*.sal" -exec rm {} \;

wellformed:
	@find . -name "*.sal" | xargs -n 1 sal-wfc \;
