BEDROCK := bedrock
MODULES := WordLemmas
VS      := $(MODULES:%=%.v)


.PHONY: coq clean

coq: Makefile.coq
	COQC='time coqc' $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R $(BEDROCK)/src Bedrock \
		     -I $(BEDROCK)/platform \
		     $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

