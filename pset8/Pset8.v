(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 8 *)

Require Import Frap Pset8Sig.

(* Prove the soundness of this Hoare Logic, with regard to the big-step semantics. *)
Theorem hoare_triple_sound : forall P c Q,
    hoare_triple P c Q ->
    (forall s s',
        P s ->
        exec s c s' ->
        Q s').
Proof.
Admitted.

(* Prove the completeness of this Hoare Logic, with regard to the big-step semantics. *)
Theorem hoare_triple_complete : forall c (P Q : assertion),
    (forall s s',
        P s ->
        exec s c s' ->
        Q s') ->
    hoare_triple P c Q.
Proof.
Admitted.
