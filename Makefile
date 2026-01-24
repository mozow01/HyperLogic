# ==============================================================================
# HyperLogic Makefile
# ==============================================================================


CONF_FILE := _CoqProject

COQ_MAKEFILE := Makefile.coq
 
all: $(COQ_MAKEFILE)
	@$(MAKE) -f $(COQ_MAKEFILE) all

$(COQ_MAKEFILE): $(CONF_FILE)
	coq_makefile -f $(CONF_FILE) -o $(COQ_MAKEFILE)

clean:
	@if [ -f $(COQ_MAKEFILE) ]; then \
		$(MAKE) -f $(COQ_MAKEFILE) clean; \
	fi
	rm -f $(COQ_MAKEFILE)
	rm -f $(COQ_MAKEFILE).conf


%: $(COQ_MAKEFILE)
	@$(MAKE) -f $(COQ_MAKEFILE) $@

.PHONY: all clean
