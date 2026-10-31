.PHONY: build check blueprint blueprint-web

build:
	lake build

check:
	bash scripts/check.sh

blueprint:
	cd blueprint/src && latexmk -pdf -interaction=nonstopmode -halt-on-error compact.tex full.tex

blueprint-web:
	cd blueprint/src && plastex --config=plastex.cfg web.tex
