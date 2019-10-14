default: site

site:
	agda --html --html-dir=docs SecureCompilation.agda && cp docs/SecureCompilation.html docs/index.html

clean:
	rm -rf docs/
