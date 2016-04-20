.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset10Sig
	$(COQC) Pset10
	$(COQC) Pset10Check

clean:
	rm *.vo
