all: draft.txt draft.html

draft.xml: draft-irtf-cfrg-bls-signature.md
	mmark draft-irtf-cfrg-bls-signature.md > draft.xml

draft.txt: draft.xml
	xml2rfc --text draft.xml

draft.html: draft.xml
	xml2rfc --html --no-external-js draft.xml -o draft.html

clean:
	rm -f draft.txt draft.html draft.xml
