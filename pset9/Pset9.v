(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 9 *)

Require Import Frap Pset9Sig.


(** * First part *)

Theorem positizer_ok : exists fsp, forall n,
  fsp ||- {{h ~> forall i, i >= n -> h $! i > 0}}
            Call "positizer" n
          {{_&h ~> forall i, h $! i > 0}}
  /\ fsp ||-- fsP.
Proof.
Admitted.


(** * Second part *)

Theorem hoare_triple_sound : forall fsp fs P {result} (c : cmd result) Q,
    fsp ||-- fs
    -> hoare_triple fsp P c Q
    -> forall h, P h
                 -> invariantFor (trsys_of fs c h)
                                 (fun p => step fs (fst p) (snd p) <> Failed).
Proof.
Admitted.
