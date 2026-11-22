TEX      := tectonic
OUT      := build
PDF      := $(OUT)/pathlaw.pdf
CONSOLE  := $(OUT)/console.txt
VENV     := numerics/.venv
PY       := $(VENV)/bin/python
STAMP    := $(VENV)/.installed
# Python 3.12 or later (numpy 2.5 needs it); override with make numerics PYTHON=...
PYTHON   ?= python3

# build/pathlaw.pdf is tracked in git. Pinning the PDF timestamp (2026-11-01 UTC)
# makes rebuilds of an unchanged source byte-identical.
export SOURCE_DATE_EPOCH := 1793491200

.PHONY: all pdf check numerics venv clean

all: pdf

pdf: $(PDF)

$(PDF): pathlaw.tex
	@mkdir -p $(OUT)
	$(TEX) --outdir $(OUT) --keep-logs pathlaw.tex

# Always rebuilds, and reads BOTH tectonic's console and the .log: an
# undefined reference reaches only the log, while an overfull box can reach
# only the console when the document reruns. Prints "clean" or every
# offending line.
check:
	@mkdir -p $(OUT)
	@$(TEX) --outdir $(OUT) --keep-logs pathlaw.tex > $(CONSOLE) 2>&1 \
	  || { cat $(CONSOLE); exit 1; }
	@if grep -hE 'LaTeX Warning|Package [A-Za-z]+ Warning|Overfull|Underfull|undefined|^warning:' \
	      $(CONSOLE) $(OUT)/pathlaw.log; then exit 1; else echo clean; fi

venv: $(STAMP)

# A stamp file inside the venv marks a finished install. Touching $(PY) instead
# would follow its symlink and change the base interpreter's timestamp.
$(STAMP): numerics/requirements.txt
	$(PYTHON) -m venv $(VENV)
	$(PY) -m pip install -q -r numerics/requirements.txt
	@touch $@

# Reproduce every measured number the paper quotes (Section 7).
numerics: $(STAMP)
	cd numerics && ./.venv/bin/python run_all.py

# Removes the logs only: build/pathlaw.pdf is tracked in git.
clean:
	rm -f $(OUT)/pathlaw.log $(CONSOLE)
