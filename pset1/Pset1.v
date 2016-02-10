(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 1 *)

Require Import Frap Pset1Sig.


Theorem allPositive_ok : forall (m : map_) (x : nat),
  allPositive m
  -> x > 0
  -> interp_map m x > 0.
Proof.
Admitted.

Theorem reduce_swap : forall e ls1 ls2, interp_reduce e (ls1 ++ ls2) = interp_reduce e (ls2 ++ ls1).
Proof.
Admitted.

Theorem interp_swap : forall e ls1 ls2, interp_mr e (ls1 ++ ls2) = interp_mr e (ls2 ++ ls1).
Proof.
Admitted.

Theorem mapReduce_partition_two : forall m r ls1 ls2, interp_mr (m, r) (ls1 ++ ls2) = interp_reduce r [interp_mr (m, r) ls1; interp_mr (m, r) ls2].
Proof.
Admitted.

Arguments app {_} _ _ .

Theorem mapReduce_partition : forall m r lsls, interp_mr (m, r) (fold_left app lsls []) = interp_reduce r (List.map (interp_mr (m, r)) lsls).
Proof.
Admitted.

(* For full credit, the code you turn in can't use [Admitted] or [admit] anymore! *)
