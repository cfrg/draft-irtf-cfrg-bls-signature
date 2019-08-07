all: draft.txt draft.html

draft.xml: draft-irtf-cfrg-bls-signature.md
	mmark -2 draft-irtf-cfrg-bls-signature.md > draft.xml

draft.txt: draft.xml
	xml2rfc --text draft.xml

draft.html: draft.xml style/addstyle.sed style/style.css
	xml2rfc --html draft.xml -o draft.html.tmp
	sed -f style/addstyle.sed < draft.html.tmp > $@
	rm -f draft.html.tmp

clean:
	rm -f draft.txt draft.html draft.xml
