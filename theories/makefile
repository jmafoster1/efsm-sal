snippets:
	isabelle build -d . snippets ;\
	sed -n '/\\snip{/,/endsnip/p' output/document/*.tex > snippets.tex ;\
	mv snippets.tex ../../verifying-trace-properties/figures/snippets.tex ;\

clean:
	@find . -name "*thy~" -exec rm {} \;
