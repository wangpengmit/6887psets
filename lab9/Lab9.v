(** * 6.887 Formal Reasoning About Programs - Lab 9
    * Mixed-Embedding Object Languages *)

Require Import Frap.

(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)

Set Implicit Arguments.
Set Asymmetric Patterns.


(* In this lab, we adapt the last mixed-embedding language from lecture,
 * removing the mutable heap and adding console input/output instead.  Prepare
 * for the unmatched excitement of typing numbers and having your verified
 * program respond with yet more numbers! *)

(* We start with a few definitions repeated from lecture. *)

Ltac simp := repeat (simplify; subst; propositional;
                    try match goal with
                        | [ H : ex _ |- _ ] => invert H
                        end); try linear_arithmetic.

Inductive loop_outcome acc :=
| Done (a : acc)
| Again (a : acc).

(* This function may come in handy later, for writing loop invariants. *)
Definition valueOf {A} (o : loop_outcome A) :=
  match o with
  | Done v => v
  | Again v => v
  end.

Inductive cmd : Set -> Type :=
| Return {result : Set} (r : result) : cmd result
| Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc
| Fail {result} : cmd result

| Input : cmd nat
| Output (v : nat) : cmd unit.
(* ^-- Note the two constructors replacing [Read] and [Write].
 * [Input] reads one number from the user.
 * [Output v] writes number [v] to the console. *)

(* Now the same notations as from class. *)
Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).

(* We replace heaps with this state type, recording all input and output actions
 * so far. *)
Record state := {
  Inputs : list nat;
  Outputs : list nat
}.

(* Now an interpreter, largely adapted from the ones we saw in lecture. *)
Inductive stepResult (result : Set) :=
| Answer (r : result)
| Stepped (s : state) (c : cmd result)
| Failed.

Implicit Arguments Failed [result].

Definition user := list nat -> nat.
(* We model the user as a deterministic function from all outputs so far to the
 * next input.  This is, of course, not a fully realistic model, but the
 * formalism that follows could quite easily be adapted to other models. *)

(* Now the small-step evaluator takes the user model as an argument. *)
Fixpoint step (u : user) {result} (c : cmd result) (s : state) : stepResult result :=
  match c with
  | Return _ r => Answer r
  | Bind _ _ c1 c2 =>
    match step u c1 s with
    | Answer r => Stepped s (c2 r)
    | Stepped s' c1' => Stepped s' (Bind c1' c2)
    | Failed => Failed
    end
  | Loop _ init body =>
    Stepped s (r <- body init;
               match r with
               | Done r' => Return r'
               | Again r' => Loop r' body
               end)
  | Fail _ => Failed

  | Input => Stepped {| Inputs := s.(Inputs) ++ u s.(Outputs) :: nil;
                        Outputs := s.(Outputs) |} (Return (u s.(Outputs)))
  | Output v => Stepped {| Inputs := s.(Inputs);
                           Outputs := s.(Outputs) ++ v :: nil |} (Return tt)
  end.

(* Time now to adapt our Hoare-triple predicate definition. *)

Definition assertion := state -> Prop.

Inductive hoare_triple (u : user) : assertion -> forall {result}, cmd result -> (result -> assertion) -> Prop :=
| HtReturn : forall P {result : Set} (v : result),
    hoare_triple u P (Return v) (fun r s => P s /\ r = v)
| HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
    hoare_triple u P c1 Q
    -> (forall r, hoare_triple u (Q r) (c2 r) R)
    -> hoare_triple u P (Bind c1 c2) R

| HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) I,
    (forall acc, hoare_triple u (I (Again acc)) (body acc) I)
    -> hoare_triple u (I (Again init)) (Loop init body) (fun r s => I (Done r) s)

| HtFail : forall {result},
    hoare_triple u (fun _ => False) (Fail (result := result)) (fun _ _ => False)

(* Input rule: looks a lot like [Write] rule from before. *)
| HtInput : forall P,
    hoare_triple u P Input (fun r s => exists s', P s'
                                                  /\ r = u s'.(Outputs)
                                                  /\ s = {| Inputs := s'.(Inputs) ++ u s'.(Outputs) :: nil;
                                                            Outputs := s'.(Outputs) |})

(* Output rule: also looks a lot like [Write] rule from before. *)  
| HtOutput : forall P v,
    hoare_triple u P (Output v) (fun _ s => exists s', P s'
                                                       /\ s = {| Inputs := s'.(Inputs);
                                                                 Outputs := s'.(Outputs) ++ v :: nil |})

| HtConsequence : forall {result} (c : cmd result) P Q (P' : assertion) (Q' : _ -> assertion),
    hoare_triple u P c Q
    -> (forall s, P' s -> P s)
    -> (forall r s, Q r s -> Q' r s)
    -> hoare_triple u P' c Q'.

(* Our new notation for Hoare triples includes an extra position for the user
 * model. *)
Notation "u ||- {{ h ~> P }} c {{ r & h' ~> Q }}" :=
  (hoare_triple u (fun h => P) c (fun r h' => Q)) (at level 70, c at next level).

(* Now, some lemma and tactic code largely copied from lecture. *)

Lemma HtStrengthen : forall u {result} (c : cmd result) P Q (Q' : _ -> assertion),
    hoare_triple u P c Q
    -> (forall r h, Q r h -> Q' r h)
    -> hoare_triple u P c Q'.
Proof.
  simplify.
  eapply HtConsequence; eauto.
Qed.

Lemma HtWeaken : forall u {result} (c : cmd result) P Q (P' : assertion),
    hoare_triple u P c Q
    -> (forall h, P' h -> P h)
    -> hoare_triple u P' c Q.
Proof.
  simplify.
  eapply HtConsequence; eauto.
Qed.

Ltac basic := apply HtReturn || eapply HtInput || eapply HtOutput.
Ltac step0 := basic || eapply HtBind || (eapply HtStrengthen; [ basic | ])
              || (eapply HtConsequence; [ apply HtFail | .. ]).
Ltac step := step0; simp.
Ltac ht := simp; repeat step.
Ltac conseq := simplify; eapply HtConsequence.
Ltac use_IH H := conseq; [ apply H | .. ]; ht.
Ltac loop_inv0 Inv := (eapply HtWeaken; [ apply HtLoop with (I := Inv) | .. ])
                      || (eapply HtConsequence; [ apply HtLoop with (I := Inv) | .. ]).
Ltac loop_inv Inv := loop_inv0 Inv; ht.


(** * Example programs *)

(* OK, let's write and verify some programs!  This one just echoes everything
 * the user types.  The loop ends if the user types "42". *)

Definition echo : cmd nat :=
  for i := 0 loop
    if i ==n 42 then
      Return (Done 42)
    else
      v <- Input;
      _ <- Output v;
      Return (Again (i+1))
  done.

(* Here's a verification that the output and input lists must match, if the
 * program terminates, assuming that they are both empty at the start. *)
Theorem echo_ok : forall u,
  u ||- {{ s ~> s.(Outputs) = nil /\ s.(Inputs) = nil }}
    echo
  {{ _&s ~> s.(Outputs) = s.(Inputs) }}.
Proof.
  unfold echo; ht.
  loop_inv (fun (_ : loop_outcome nat) s => s.(Outputs) = s.(Inputs)).
  cases (acc ==n 42); ht.
  equality.
  equality.
Qed.

(* Another program: input a number [n] and then print all numbers from [0] to
 * [n-1]. *)
Definition print_upto : cmd (nat * nat) :=
  n <- Input;
  for p := (0, n) loop
    if fst p ==n snd p then
      Return (Done p)
    else
      _ <- Output (fst p);
      Return (Again (S (fst p), snd p))
  done.

(* Our last example program: keep reading numbers from the user, at each step
 * printing the sum of all numbers read so far.  Exit on 42. *)
Definition sum_up : cmd nat :=
  for i := 0 loop
    if i ==n 42 then
      Return (Done 42)
    else
      v <- Input;
      _ <- Output (i + v);
      Return (Again (i + v))
  done.

(* This next command generates OCaml code from our examples. *)
Extraction "Lab9.ml" echo print_upto sum_up.
(* If you happen to have OCaml installed, you can trying running these programs,
 * using the provided Lab9Interp.ml file!  We also give a Makefile so that you
 * can run the programs with:
 *   make run_echo
 *   make run_print_upto
 *   make run_sum_up
 * However, the proof stuff that follows is independent of all that. *)

(* CHALLENGE #1: verify [print_upto]. *)

Fixpoint upto (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => upto n' ++ n' :: nil
  end.

Theorem print_upto_ok : forall u,
  u ||- {{ s ~> s.(Outputs) = nil /\ s.(Inputs) = nil }}
    print_upto
  {{ _&s ~> exists n, s.(Inputs) = n :: nil /\ s.(Outputs) = upto n }}.
Proof.
Admitted.

(* CHALLENGE #2: verify [sum_up]. *)

(* It may come in handy to use this function. *)
Definition sum (ls : list nat) :=
  fold_left plus ls 0.

(* However, this is the one we use in the spec. *)
Fixpoint sumsOf (ls : list nat) (acc : nat) : list nat :=
  match ls with
  | nil => nil
  | n :: ls => (n + acc) :: sumsOf ls (n + acc)
  end.

Theorem sum_up_ok : forall u,
  u ||- {{ s ~> s.(Outputs) = nil /\ s.(Inputs) = nil }}
    sum_up
  {{ _&s ~> s.(Outputs) = sumsOf s.(Inputs) 0 }}.
Proof.
Admitted.

(* Our proof of this theorem depends on several inductively proved lemmas. *)


(** * Soundness proof *)

(* We define how to build transition systems out of programs, in roughly the
 * same way as before.  Note that the user becomes part of the transition
 * system! *)
Definition trsys_of (u : user) {result} (c : cmd result) (s : state) := {|
  Initial := {(c, s)};
  Step := fun p1 p2 => step u (fst p1) (snd p1) = Stepped (snd p2) (fst p2)
|}.

(* CHALLENGE #3: prove the Hoare-triple predicate sound with respect to these
 * transition systems.  As a starting point, you probably want to copy and paste
 * the proof of a related fact from the file DeepAndShallowEmbeddings.v that we
 * went through in lecture.  That file contains several modules with successive
 * variants of the logic; the final one (the last [hoare_triple_sound] theorem
 * in the file) is closest to our example here, making it the best starting
 * point. *)

Theorem hoare_triple_sound : forall u P {result} (c : cmd result) Q,
    hoare_triple u P c Q
    -> forall s, P s
                 -> invariantFor (trsys_of u c s)
                                 (fun p => step u (fst p) (snd p) <> Failed).
Proof.
Admitted.
