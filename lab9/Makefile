.PHONY: run_%

run_%.ml: Lab9.ml Lab9Interp.ml
	cat $? >$@
	echo "let _ = interp (Obj.magic $*)" >>$@

run_%: run_%.ml
	ocaml $<
