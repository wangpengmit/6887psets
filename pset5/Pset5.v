(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 5 *)

Require Import Frap AbstractInterpret Pset5Sig.

(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)


Theorem constant_sound : absint_sound constant_absint.
Proof.
Admitted.

Theorem constfold_cmd_fwd : forall ss v c v' c',
    (forall v' c', step^* (v, c) (v', c')
                   -> exists s, ss $? c' = Some s
                                /\ compatible s v')
    -> step^* (v, c) (v', c')
    -> step^* (v, constfold_cmd c ss (fun c1 => c1))
           (v', constfold_cmd c' ss (fun c1 => c1)).
Proof.
Admitted.

Theorem constfold_cmd_fwd_big : forall ss v c v',
    (forall v' c', step^* (v, c) (v', c')
                   -> exists s, ss $? c' = Some s
                                /\ compatible s v')
    -> eval v c v'
    -> eval v (constfold_cmd c ss (fun c1 => c1)) v'.
Proof.
Admitted.


(** * An example, analyzing one program *)

Theorem optimize_program_ok : forall v c v' ss,
  eval v c v'
  -> invariantFor (absint_trsys constant_absint c)
                  (fun p => exists s, ss $? snd p = Some s
                                      /\ subsumed (fst p) s)
  -> eval v (constfold_cmd c ss (fun c1 => c1)) v'.
Proof.
  simplify.
  apply constfold_cmd_fwd_big; auto.
  eapply invariant_simulates with (sys1 := trsys_of v c) in H0;
    try (apply absint_simulates with (a := constant_absint); apply constant_sound).
  simplify.
  eapply use_invariant in H0; simplify; eauto.
  invert H0.
  invert H2.
  simplify.
  first_order.
  eauto.
Qed.

Example loopsy :=
  "a" <- 7;;
  "b" <- 0;;
  while "n" loop
    "b" <- "b" + "a";;
    "n" <- "n" - 1
  done.

Example loopsy_optimized :=
  "a" <- 7;;
  "b" <- 0;;
  while "n" loop
    "b" <- "b" + 7;;
    "n" <- "n" - 1
  done.

Theorem loopsy_optimized_properly : forall v v',
  eval v loopsy v'
  -> eval v loopsy_optimized v'.
Proof.
  simplify.
  assert (exists ss, invariantFor (absint_trsys constant_absint loopsy)
                                  (fun p => exists s, ss $? snd p = Some s
                                                      /\ subsumed (fst p) s)
                     /\ loopsy_optimized = constfold_cmd loopsy ss (fun c1 => c1)).

  eexists; propositional.
  
  apply interpret_sound.
  apply constant_sound.

  unfold loopsy.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret_done.

  simplify.
  equality.

  first_order.
  rewrite H1.
  apply optimize_program_ok.
  assumption.
  assumption.
Qed.
