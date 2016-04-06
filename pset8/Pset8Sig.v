(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 8 *)

Require Import Frap.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)

(* In class, we learned about a version of Hoare logic where every loop has an
 * invariant written right on it.  Hoare logic can also be defined over
 * completely conventional program syntax, where the person writing the proof
 * chooses a suitable invariant on every invocation of the loop rule.  This
 * style may be more appealing for its clear separation of the program
 * correctness property (the precondition and postcondition) from the
 * correctness argument (including loop invariants).  And we can still prove the
 * key *soundness* theorem for this logic, which will be your first task in this
 * problem set.  It also becomes easier to state a *completeness* property:
 * every true specification is provable, using just the Hoare-logic rules.
 * Proof of that fact will be your second task, and it will require some
 * different ingredients than in the soundness proof. *)

(* Let's start with a big-step semantics for the no-loop-invariants imperative
 * language.  The language we will use is a simplified version of the one in
 * class, stripping away heap operations. *)
Inductive exp :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : exp)
| Minus (e1 e2 : exp).

(* Boolean expression syntax *)
Inductive test :=
| Eq (e1 e2 : exp)
| NotEq (e1 e2 : exp).

Inductive cmd :=
| Assign (x : var) (e : exp)
| Seq (c1 c2 : cmd)
| If (b : test) (c1 c2 : cmd)
| While (b : test) (c1 : cmd)
(* ^-- As promised, no invariant on a loop! *)
| Skip.

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).

Fixpoint eval (e : exp) (s : fmap var nat) : nat :=
  match e with
    | Const n => n
    | Var x => s $! x
    | Plus e1 e2 => eval e1 s + eval e2 s
    | Minus e1 e2 => eval e1 s - eval e2 s
  end.

Definition beval (b : test) (s : fmap var nat) : bool :=
  match b with
    | Eq e1 e2 => beq_nat (eval e1 s) (eval e2 s)
    | NotEq e1 e2 => negb (beq_nat (eval e1 s) (eval e2 s))
  end.

(* Big-step semantics for commands *)
Inductive exec : fmap var nat -> cmd -> fmap var nat -> Prop :=
| ExecAssign : forall s x e,
  exec s (Assign x e) (s $+ (x, eval e s))
| ExecSeq : forall s1 c1 c2 s2 s3,
  exec s1 c1 s2
  -> exec s2 c2 s3
  -> exec s1 (Seq c1 c2) s3
| ExecIfTrue : forall s1 b c1 c2 s2,
  beval b s1 = true
  -> exec s1 c1 s2
  -> exec s1 (If b c1 c2) s2
| ExecIfFalse : forall s1 b c1 c2 s2,
  beval b s1 = false
  -> exec s1 c2 s2
  -> exec s1 (If b c1 c2) s2
| ExecWhileTrue : forall s1 b c1 s2 s3,
  beval b s1 = true
  -> exec s1 c1 s2
  -> exec s2 (While b c1) s3
  -> exec s1 (While b c1) s3
| ExecWhileFalse : forall s b c1,
  beval b s = false
  -> exec s (While b c1) s
| ExecSkip : forall s,
    exec s Skip s.

Hint Constructors exec.

Notation valuation := (fmap var nat).
Notation assertion := (valuation -> Prop).

(* Now for the Hoare-triple rules.  Remember that in class we followed a
 * 'postcondition calculator' style of defining Hoare triple rules, where in
 * each case we allow the precondition to be an arbitrary assertion and
 * constrain the form of the postcondition. Here we reverse the direction,
 * following a 'precondition calculator' style of allowing arbitrary
 * postcondition, except for the [While] case. *)
Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
| HtAssign : forall P x e,
    hoare_triple (fun s => P (s $+ (x, eval e s))) (Assign x e) P
    (* Note how the precondition is built from the postcondition by,
     * essentially, "simulating the effect of the assignment ahead of time." *)

| HtIf : forall P Q b c1 c2,
    hoare_triple (fun s => P s /\ beval b s = true) c1 Q
    -> hoare_triple (fun s => P s /\ beval b s = false) c2 Q
    -> hoare_triple P (If b c1 c2) Q
    (* This rule avoids the disjunction we used last time around. *)

| HtWhile : forall P b c,
    hoare_triple (fun s => P s /\ beval b s = true) c P
    -> hoare_triple P (While b c) (fun s => P s /\ beval b s = false)
    (* Here we use the precondition as the loop invariant.  In practice, of
     * course, the "immediate" precondition isn't suitable as an invariant, in
     * which case the consequence rule below becomes even more important,
     * to wrap a proof with an invariant installed as precondition. *)

(* The last three rules are unchanged. *)
| HtSeq : forall R P Q c1 c2,
    hoare_triple P c1 R
    -> hoare_triple R c2 Q
    -> hoare_triple P (Seq c1 c2) Q
| HtSkip : forall P : assertion,
    hoare_triple P Skip P
| HtConsequence : forall (P Q P' Q' : assertion) c,
    hoare_triple P c Q
    -> (forall s, P' s -> P s)
    -> (forall s, Q s -> Q' s)
    -> hoare_triple P' c Q'.

(* Some automation help: you may appreciate these lemmas and tactics. *)

Lemma HtStrengthenPre : forall (P Q P' : assertion) c,
  hoare_triple P c Q
  -> (forall v, P' v -> P v)
  -> hoare_triple P' c Q.
Proof.
  simplify; eapply HtConsequence; eauto.
Qed.

Lemma HtStrengthenPost : forall (P Q Q' : assertion) c,
  hoare_triple P c Q
  -> (forall v, Q v -> Q' v)
  -> hoare_triple P c Q'.
Proof.
  simplify; eapply HtConsequence; eauto.
Qed.

Ltac ht1 := apply HtSkip || apply HtAssign || eapply HtSeq
            || eapply HtIf || eapply HtWhile
            || eapply HtStrengthenPre
            || eapply HtStrengthenPost.

Ltac t := cbv beta; propositional; subst;
          repeat match goal with
                 | [ H : ex _ |- _ ] => invert H; propositional; subst
                 end;
          simplify;
          repeat match goal with
                 | [ _ : context[?a <=? ?b] |- _ ] => destruct (a <=? b); try discriminate
                 | [ H : ?E = ?E |- _ ] => clear H
                 end; simplify; propositional; auto; try equality; try linear_arithmetic.

Ltac ht := simplify; repeat ht1; t.

Module Type S.
  
  (* Prove the soundness of this Hoare Logic with regard to the big-step
   * semantics: when we prove a program with respect to a
   * precondition-postcondition pair, it really does follow that spec. *)
  Axiom hoare_triple_sound : forall P c Q,
    hoare_triple P c Q ->
    (forall s s',
        P s ->
        exec s c s' ->
        Q s').

  (* Prove the completeness of this Hoare Logic with regard to the big-step
   * semantics: given any legitimate pre/postcondition, we can establish a Hoare
   * triple using them. *)
  Axiom hoare_triple_complete : forall c (P Q : assertion),
      (forall s s',
          P s ->
          exec s c s' ->
          Q s') ->
      hoare_triple P c Q.

End S.
