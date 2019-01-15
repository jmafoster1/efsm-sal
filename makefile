DOT_FILES = $(shell find -type f -name '*.dot')
DATE=`date +'%d/%m/%y'`


dot:
	@ for b in $(basename $(DOT_FILES)) ; do \
		firstString="I love Suzi and Marry" ;\
		secondString="Sara" ;\
		echo "${firstString/Suzi/$secondString}" ; \
	  # dot -T pdf -o ../pdfs/$$b.pdf $$b.dot ; \
	done

eod:
	git add -A ; \
	git commit -m "end of day $(DATE)" ; \
	git push origin master ; \
