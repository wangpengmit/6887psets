.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset6Sig
	$(COQC) Pset6
	$(COQC) Pset6Check

clean:
	rm *.vo
