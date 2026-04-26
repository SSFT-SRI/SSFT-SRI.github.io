.PHONY: build deploy

build:
	emacs --batch --quick --load build-site.el

deploy: build
	git diff --check
	@printf "Org export complete. Commit and push the Org sources, generated HTML, style.css, and build-site.el to publish on GitHub Pages.\n"
