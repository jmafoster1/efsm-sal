snippets:
	isabelle build -d . snippets ;\
	sed -n '/\\snip{/,/endsnip/p' output/document/Coin_Tea.tex > snippets.tex ;\
	sed -n '/\\snip{/,/endsnip/p' output/document/XXXlinkedin_ext_fixed.tex >> snippets.tex ;\
	mv snippets.tex ../../verifying-trace-properties/figures/snippets.tex ;\

clean:
	@find . -name "*thy~" -exec rm {} \;
