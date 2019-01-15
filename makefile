DOT_FILES = $(shell find ./ -type f -name '*.dot')
DATE=`date +'%d/%m/%y'`


dot:
	@ for b in $(basename $(DOT_FILES)) ; do \
	  dot -T pdf -o $$b.pdf $$b.dot ; \
	done
	@ mv dotfiles/*.pdf pdfs/

eod:
	git add -A ; \
	git commit -m "end of day $(DATE)" ; \
	git push origin master ; \
