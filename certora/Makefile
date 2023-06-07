default: help

CONTRACTS_DIR = ../src
LIBS_DIR = ../lib

help:
	@echo "usage:"
	@echo "  make restore: reverts all unstaged changes in the src directory"
	@echo "  make bug: generates a patch containing a manually injected bug"

.SILENT: bug
bug:
	#git diff origin/certora -- $(CONTRACTS_DIR) > tests/participants/bug$$(ls -1 tests/participants | grep -Eo '^bug[0-9]+' | sort -n | tail -1 | tr -cd '[:digit:]' | awk 'END{print $$0 + 1}').patch
	git diff origin/certora -- $(CONTRACTS_DIR) > tests/participants/bug12.patch

restore:
	git restore $(CONTRACTS_DIR)/*
