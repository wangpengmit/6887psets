.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap

coq:
	$(COQC) Pset0Sig
	$(COQC) Pset0
	$(COQC) Pset0Check

clean:
	rm *.vo
