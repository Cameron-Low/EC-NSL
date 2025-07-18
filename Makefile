# -*- Makefile -*-

# --------------------------------------------------------------------
ECJOBS   ?= 2
ECCONF   := config/tests.config
CHECKS   ?= nsl

ECCHECK := easycrypt runtest

# --------------------------------------------------------------------
.PHONY: default usage check

default: check

usage:
	@echo "Usage: make check" >&2

check:
	$(ECCHECK) $(ECCONF) $(CHECKS)
