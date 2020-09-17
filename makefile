DOT_FILES = $(shell find ./ -type f -name '*.dot')
DATE=`date +'%d/%m/%y'`

dot:
	@ for b in $(basename $(DOT_FILES)) ; do \
	  dot -T pdf -o $$b.pdf $$b.dot ; \
	done

eod:
	git add -A ; \
	git commit -m "end of day $(DATE)" ; \
	git push origin master ; \

snippets:
	isabelle build -D.; \
	sed -n '/\\snip{/,/endsnip/p' output/document/*.tex > snippets-ltl.tex; \
