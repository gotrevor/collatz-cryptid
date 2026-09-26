# From the repository root: make -f docs/overview.mk
# OVERVIEW.md and overview.dot are canonical; HTML/SVG are generated.
.PHONY: all
all: OVERVIEW.html

docs/overview.svg: docs/overview.dot
	dot -Tsvg $< -o $@

OVERVIEW.html: OVERVIEW.md docs/overview.svg docs/overview.css docs/overview.mk
	pandoc OVERVIEW.md --from=markdown --standalone --embed-resources --css=docs/overview.css --metadata=lang:en --metadata=pagetitle:"Project overview" --output=$@
