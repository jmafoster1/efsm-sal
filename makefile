build:
	@mkdir -p jars
	javac -d build src/dot2isabelle/*.java; \
	javac -d build src/isabelle2sal/*.java; \
	javac -d build src/sal2isabelle/*.java; \
	cd build; \
	jar -cfm  ../jars/dot2isabelle.jar ../src/dot2isabelle/manifest.mf dot2isabelle; \
	jar -cfm  ../jars/isabelle2sal.jar ../src/isabelle2sal/manifest.mf isabelle2sal; \
	jar -cfm  ../jars/sal2isabelle.jar ../src/sal2isabelle/manifest.mf sal2isabelle; \

clean:
	@rm -r jars build
