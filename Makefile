.PHONY: all paper checks lean lint format
PYTHON ?= python3

all: lint checks lean paper

paper:
	./paper/build.sh

checks:
	mkdir -p work
	$(PYTHON) -I checks/audit_low_logit_rank.py work/audit_low_logit_rank_results.json
	cmp work/audit_low_logit_rank_results.json checks/audit_low_logit_rank_results.json

lean:
	cd formalization && $(PYTHON) verify.py

lint:
	$(PYTHON) -m ruff check .
	$(PYTHON) -m ruff format --check .
	cffconvert --validate

format:
	$(PYTHON) -m ruff check --fix .
	$(PYTHON) -m ruff format .
