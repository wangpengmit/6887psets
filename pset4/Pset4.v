(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 4 *)

Require Import Frap Pset4Sig.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)


Section env.

  Variable env : environment.
  
  Theorem big_small : forall v c v',
      eval env v c (Normal, v')
      -> (step env)^* (v, c) (v', Skip).
  Proof.
  Admitted.

  Theorem big_small_exn : forall v c n v',
      eval env v c (Exception n, v')
      -> (step env)^* (v, c) (v', Throw (Const n)).
  Proof.
  Admitted.

  Theorem small_big : forall v c v',
      (step env)^* (v, c) (v', Skip)
      -> eval env v c (Normal, v').
  Proof.
  Admitted.

  Theorem small_big_exn : forall v c v' n,
      (step env)^* (v, c) (v', Throw (Const n))
      -> eval env v c (Exception n, v').
  Proof.
  Admitted.

  (** Small-step semantics with control stack *)

  Theorem eval_stepcs : forall v c v',
      eval env v c (Normal, v')
      -> (stepcs env)^* ([], v, c, Skip) ([], v', Skip, Skip).
  Proof.
  Admitted.

  Theorem eval_stepcs_exn : forall v c (n : nat) v',
      eval env v c (Exception n, v')
      -> (stepcs env)^* ([], v, c, Skip) ([], v', Throw (Const n), Skip).
  Proof.
  Admitted.

  Theorem stepcs_eval : forall v c v',
      (stepcs env)^* ([], v, c, Skip) ([], v', Skip, Skip)
      -> eval env v c (Normal, v').
  Proof.
  Admitted.

  Theorem stepcs_eval_exn : forall v c v' (n : nat),
      (stepcs env)^* ([], v, c, Skip) ([], v', Throw (Const n), Skip)
      -> eval env v c (Exception n, v').
  Proof.
  Admitted.

End env.
