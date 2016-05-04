(** * 6.887 Formal Reasoning About Programs - Lab 12
    * Concurrent Separation Logic *)

Require Import Frap Setoid Classes.Morphisms SepCancel.

(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)

Set Implicit Arguments.
Set Asymmetric Patterns.

(* This lab is pure practice verifying specific programs with Concurrent
 * Separation Logic.  We first copy a bunch of content from the lecture code.
 * Skip ahead to the text "Examples" to see the lab material that we ask you to
 * work through. *)

(** * Shared notations and definitions; main material starts afterward. *)

Notation heap := (fmap nat nat).
Notation locks := (set nat).

Hint Extern 1 (_ <= _) => linear_arithmetic.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic.

Ltac simp := repeat (simplify; subst; propositional;
                     try match goal with
                         | [ H : ex _ |- _ ] => invert H
                         end); try linear_arithmetic.


(** * A shared-memory concurrent language with loops *)

Inductive loop_outcome acc :=
| Done (a : acc)
| Again (a : acc).

Definition valueOf {A} (o : loop_outcome A) :=
  match o with
  | Done v => v
  | Again v => v
  end.

Inductive cmd : Set -> Type :=
| Return {result : Set} (r : result) : cmd result
| Fail {result} : cmd result
| Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc

| Read (a : nat) : cmd nat
| Write (a v : nat) : cmd unit
| Lock (a : nat) : cmd unit
| Unlock (a : nat) : cmd unit
| Alloc (numWords : nat) : cmd nat
| Free (base numWords : nat) : cmd unit

| Par (c1 c2 : cmd unit) : cmd unit.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).
Infix "||" := Par.

Fixpoint initialize (h : heap) (base numWords : nat) : heap :=
  match numWords with
  | O => h
  | S numWords' => initialize h base numWords' $+ (base + numWords', 0)
  end.

Fixpoint deallocate (h : heap) (base numWords : nat) : heap :=
  match numWords with
  | O => h
  | S numWords' => deallocate (h $- base) (base+1) numWords'
  end.

Inductive step : forall A, heap * locks * cmd A -> heap * locks * cmd A -> Prop :=
| StepBindRecur : forall result result' (c1 c1' : cmd result') (c2 : result' -> cmd result) h l h' l',
  step (h, l, c1) (h', l', c1')
  -> step (h, l, Bind c1 c2) (h', l', Bind c1' c2)
| StepBindProceed : forall (result result' : Set) (v : result') (c2 : result' -> cmd result) h l,
  step (h, l, Bind (Return v) c2) (h, l, c2 v)

| StepLoop : forall (acc : Set) (init : acc) (body : acc -> cmd (loop_outcome acc)) h l,
  step (h, l, Loop init body) (h, l, o <- body init; match o with
                                                     | Done a => Return a
                                                     | Again a => Loop a body
                                                     end)

| StepRead : forall h l a v,
  h $? a = Some v
  -> step (h, l, Read a) (h, l, Return v)
| StepWrite : forall h l a v v',
  h $? a = Some v
  -> step (h, l, Write a v') (h $+ (a, v'), l, Return tt)
| StepAlloc : forall h l numWords a,
  a <> 0
  -> (forall i, i < numWords -> h $? (a + i) = None)
  -> step (h, l, Alloc numWords) (initialize h a numWords, l, Return a)
| StepFree : forall h l a numWords,
  step (h, l, Free a numWords) (deallocate h a numWords, l, Return tt)

| StepLock : forall h l a,
  ~a \in l
  -> step (h, l, Lock a) (h, l \cup {a}, Return tt)
| StepUnlock : forall h l a,
  a \in l
  -> step (h, l, Unlock a) (h, l \setminus {a}, Return tt)

| StepPar1 : forall h l c1 c2 h' l' c1',
  step (h, l, c1) (h', l', c1')
  -> step (h, l, Par c1 c2) (h', l', Par c1' c2)
| StepPar2 : forall h l c1 c2 h' l' c2',
  step (h, l, c2) (h', l', c2')
  -> step (h, l, Par c1 c2) (h', l', Par c1 c2').
    
Definition trsys_of (h : heap) (l : locks) {result} (c : cmd result) := {|
  Initial := {(h, l, c)};
  Step := step (A := result)
|}.

Module Import S <: SEP.
  Definition hprop := heap -> Prop.

  Definition himp (p q : hprop) := forall h, p h -> q h.
  Definition heq (p q : hprop) := forall h, p h <-> q h.

  Definition lift (P : Prop) : hprop :=
    fun h => P /\ h = $0.

  Definition star (p q : hprop) : hprop :=
    fun h => exists h1 h2, split h h1 h2 /\ disjoint h1 h2 /\ p h1 /\ q h2.

  Definition exis A (p : A -> hprop) : hprop :=
    fun h => exists x, p x h.

  Notation "[| P |]" := (lift P) : sep_scope.
  Infix "*" := star : sep_scope.
  Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
  Delimit Scope sep_scope with sep.
  Notation "p === q" := (heq p%sep q%sep) (no associativity, at level 70).
  Notation "p ===> q" := (himp p%sep q%sep) (no associativity, at level 70).

  Local Open Scope sep_scope.

  Lemma iff_two : forall A (P Q : A -> Prop),
    (forall x, P x <-> Q x)
    -> (forall x, P x -> Q x) /\ (forall x, Q x -> P x).
  Proof.
    firstorder.
  Qed.

  Local Ltac t := (unfold himp, heq, lift, star, exis; propositional; subst);
                 repeat (match goal with
                         | [ H : forall x, _ <-> _ |- _  ] =>
                           apply iff_two in H
                         | [ H : ex _ |- _ ] => destruct H
                         | [ H : split _ _ $0 |- _ ] => apply split_empty_fwd in H
                         end; propositional; subst); eauto 15.

  Theorem himp_heq : forall p q, p === q
    <-> (p ===> q /\ q ===> p).
  Proof.
    t.
  Qed.

  Theorem himp_refl : forall p, p ===> p.
  Proof.
    t.
  Qed.

  Theorem himp_trans : forall p q r, p ===> q -> q ===> r -> p ===> r.
  Proof.
    t.
  Qed.

  Theorem lift_left : forall p (Q : Prop) r,
    (Q -> p ===> r)
    -> p * [| Q |] ===> r.
  Proof.
    t.
  Qed.

  Theorem lift_right : forall p q (R : Prop),
    p ===> q
    -> R
    -> p ===> q * [| R |].
  Proof.
    t.
  Qed.

  Hint Resolve split_empty_bwd'.

  Theorem extra_lift : forall (P : Prop) p,
    P
    -> p === [| P |] * p.
  Proof.
    t.
    apply split_empty_fwd' in H1; subst; auto.
  Qed.    

  Theorem star_comm : forall p q, p * q === q * p.
  Proof.
    t.
  Qed.

  Theorem star_assoc : forall p q r, p * (q * r) === (p * q) * r.
  Proof.
    t.
  Qed.

  Theorem star_cancel : forall p1 p2 q1 q2, p1 ===> p2
    -> q1 ===> q2
    -> p1 * q1 ===> p2 * q2.
  Proof.
    t.
  Qed.

  Theorem exis_gulp : forall A p (q : A -> _),
    p * exis q === exis (fun x => p * q x).
  Proof.
    t.
  Qed.

  Theorem exis_left : forall A (p : A -> _) q,
    (forall x, p x ===> q)
    -> exis p ===> q.
  Proof.
    t.
  Qed.

  Theorem exis_right : forall A p (q : A -> _) x,
    p ===> q x
    -> p ===> exis q.
  Proof.
    t.
  Qed.
End S.

Export S.
Module Import Se := SepCancel.Make(S).


(* ** Some extra predicates outside the set that the engine knows about *)

Definition heap1 (a v : nat) : heap := $0 $+ (a, v).
Definition ptsto (a v : nat) : hprop :=
  fun h => h = heap1 a v.

Notation "[| P |]" := (lift P) : sep_scope.
Notation emp := (lift True).
Infix "*" := star : sep_scope.
Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
Delimit Scope sep_scope with sep.
Notation "p === q" := (heq p%sep q%sep) (no associativity, at level 70).
Notation "p ===> q" := (himp p%sep q%sep) (no associativity, at level 70).
Infix "|->" := ptsto (at level 30) : sep_scope.

Fixpoint multi_ptsto (a : nat) (vs : list nat) : hprop :=
  match vs with
  | nil => emp
  | v :: vs' => a |-> v * multi_ptsto (a + 1) vs'
  end%sep.

Infix "|-->" := multi_ptsto (at level 30) : sep_scope.

Fixpoint zeroes (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => zeroes n' ++ 0 :: nil
  end.

Fixpoint allocated (a n : nat) : hprop :=
  match n with
  | O => emp
  | S n' => (exists v, a |-> v) * allocated (a+1) n'
  end%sep.

Infix "|->?" := allocated (at level 30) : sep_scope.


(** * Finally, the Hoare logic *)

Inductive hoare_triple (linvs : list hprop) : forall {result}, hprop -> cmd result -> (result -> hprop) -> Prop :=

| HtReturn : forall P {result : Set} (v : result),
    hoare_triple linvs P (Return v) (fun r => P * [| r = v |])%sep
| HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
    hoare_triple linvs P c1 Q
    -> (forall r, hoare_triple linvs (Q r) (c2 r) R)
    -> hoare_triple linvs P (Bind c1 c2) R
| HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) I,
    (forall acc, hoare_triple linvs (I (Again acc)) (body acc) I)
    -> hoare_triple linvs (I (Again init)) (Loop init body) (fun r => I (Done r))
| HtFail : forall {result},
    hoare_triple linvs [| False |]%sep (Fail (result := result)) (fun _ => [| False |])%sep
| HtRead : forall a R,
    hoare_triple linvs (exists v, a |-> v * R v)%sep (Read a) (fun r => a |-> r * R r)%sep
| HtWrite : forall a v',
    hoare_triple linvs (exists v, a |-> v)%sep (Write a v') (fun _ => a |-> v')%sep
| HtAlloc : forall numWords,
    hoare_triple linvs emp%sep (Alloc numWords) (fun r => r |--> zeroes numWords * [| r <> 0 |])%sep
| HtFree : forall a numWords,
    hoare_triple linvs (a |->? numWords)%sep (Free a numWords) (fun _ => emp)%sep

| HtLock : forall a I,
    nth_error linvs a = Some I
    -> hoare_triple linvs emp%sep (Lock a) (fun _ => I)
| HtUnlock : forall a I,
    nth_error linvs a = Some I
    -> hoare_triple linvs I (Unlock a) (fun _ => emp)%sep

| HtPar : forall P1 c1 Q1 P2 c2 Q2,
    hoare_triple linvs P1 c1 Q1
    -> hoare_triple linvs P2 c2 Q2
    -> hoare_triple linvs (P1 * P2)%sep (Par c1 c2) (fun _ => Q1 tt * Q2 tt)%sep

| HtConsequence : forall {result} (c : cmd result) P Q (P' : hprop) (Q' : _ -> hprop),
    hoare_triple linvs P c Q
    -> P' ===> P
    -> (forall r, Q r ===> Q' r)
    -> hoare_triple linvs P' c Q'
| HtFrame : forall {result} (c : cmd result) P Q R,
    hoare_triple linvs P c Q
    -> hoare_triple linvs (P * R)%sep c (fun r => Q r * R)%sep.

Notation "linvs ||- {{ P }} c {{ r ~> Q }}" :=
  (hoare_triple linvs P%sep c (fun r => Q%sep)) (at level 90, c at next level).

Lemma HtStrengthen : forall linvs {result} (c : cmd result) P Q (Q' : _ -> hprop),
    hoare_triple linvs P c Q
    -> (forall r, Q r ===> Q' r)
    -> hoare_triple linvs P c Q'.
Proof.
  simplify.
  eapply HtConsequence; eauto.
  reflexivity.
Qed.

Lemma HtWeaken : forall linvs {result} (c : cmd result) P Q (P' : hprop),
    hoare_triple linvs P c Q
    -> P' ===> P
    -> hoare_triple linvs P' c Q.
Proof.
  simplify.
  eapply HtConsequence; eauto.
  reflexivity.
Qed.


(** * Automation tactics *)

Opaque heq himp lift star exis ptsto.

Theorem use_lemma : forall linvs result P' (c : cmd result) (Q : result -> hprop) P R,
  hoare_triple linvs P' c Q
  -> P ===> P' * R
  -> hoare_triple linvs P c (fun r => Q r * R)%sep.
Proof.
  simp.
  eapply HtWeaken.
  eapply HtFrame.
  eassumption.
  eauto.
Qed.

Theorem HtRead' : forall linvs a v,
  hoare_triple linvs (a |-> v)%sep (Read a) (fun r => a |-> v * [| r = v |])%sep.
Proof.
  simp.
  apply HtWeaken with (exists r, a |-> r * [| r = v |])%sep.
  eapply HtStrengthen.
  apply HtRead.
  simp.
  cancel; auto.
  subst; cancel.
  cancel; auto.
Qed.

Theorem HtRead'' : forall linvs p P R,
  P ===> (exists v, p |-> v * R v)
  -> hoare_triple linvs P (Read p) (fun r => p |-> r * R r)%sep.
Proof.
  simp.
  eapply HtWeaken.
  apply HtRead.
  assumption.
Qed.

Lemma HtReturn' : forall linvs P {result : Set} (v : result) Q,
    P ===> Q v
    -> hoare_triple linvs P (Return v) Q.
Proof.
  simp.
  eapply HtStrengthen.
  constructor.
  simp.
  cancel.
Qed.

Ltac basic := apply HtReturn' || eapply HtWrite || eapply HtAlloc || eapply HtFree
              || (eapply HtLock; simplify; solve [ eauto ])
              || (eapply HtUnlock; simplify; solve [ eauto ]).
Ltac step0 := basic || eapply HtBind || (eapply use_lemma; [ basic | cancel ])
              || (eapply use_lemma; [ eapply HtRead' | solve [ cancel; auto ] ])
              || (eapply HtRead''; solve [ cancel ])
              || (eapply HtStrengthen; [ eapply use_lemma; [ basic | cancel ] | ])
              || (eapply HtConsequence; [ apply HtFail | .. ]).
Ltac step := step0; simp.
Ltac ht := simp; repeat step.
Ltac conseq := simplify; eapply HtConsequence.
Ltac use_IH H := conseq; [ apply H | .. ]; ht.
Ltac loop_inv0 Inv := (eapply HtWeaken; [ apply HtLoop with (I := Inv) | .. ])
                      || (eapply HtConsequence; [ apply HtLoop with (I := Inv) | .. ]).
Ltac loop_inv Inv := loop_inv0 Inv; ht.
Ltac fork0 P1 P2 := apply HtWeaken with (P := (P1 * P2)%sep); [ apply HtPar | ].
Ltac fork P1 P2 := fork0 P1 P2 || (eapply HtStrengthen; [ fork0 P1 P2 | ]).
Ltac use H := (eapply use_lemma; [ eapply H | cancel ])
              || (eapply HtStrengthen; [ eapply use_lemma; [ eapply H | cancel ] | ]).

Ltac heq := intros; apply himp_heq; split.

Instance hoare_triple_morphism : forall linvs A,
  Proper (heq ==> eq ==> (eq ==> heq) ==> iff) (@hoare_triple linvs A).
Proof.
  Transparent himp.
  repeat (hnf; intros).
  unfold pointwise_relation in *; intuition subst.

  eapply HtConsequence; eauto.
  rewrite H; reflexivity.
  intros.
  hnf in H1.
  specialize (H1 r _ eq_refl).
  rewrite H1; reflexivity.

  eapply HtConsequence; eauto.
  rewrite H; reflexivity.
  intros.
  hnf in H1.
  specialize (H1 r _ eq_refl).
  rewrite H1; reflexivity.
  Opaque himp.
Qed.

Theorem try_ptsto_first : forall a v, try_me_first (ptsto a v).
Proof.
  simplify.
  apply try_me_first_easy.
Qed.

Hint Resolve try_ptsto_first.


(** * Examples *)

(* We'll be working with pointer-based binary trees.  Here's a definition of the
 * functional version of trees, with data in internal nodes but not leaves. *)
Inductive tree :=
| Leaf
| Node (l : tree) (data : nat) (r : tree).

(* And here's a predicate explaining how a functional tree might be laid out in
 * memory with pointers.  (It may seem familiar from a past pset!) *)
Fixpoint mtree (p : nat) (t : tree) :=
  match t with
  | Leaf => [| p = 0 |]
  | Node l data r => [| p <> 0 |]
                     * exists lp rp, p |--> [lp; data; rp]
                                     * mtree lp l
                                     * mtree rp r
  end%sep.

(* We can prove two basic lemmas about trees, for when their root pointers are
 * null or nonnull, respectively. *)

Theorem mtree_null : forall t,
  mtree 0 t === [| t = Leaf |].
Proof.
  heq; cases t; cancel.
Qed.

Theorem mtree_nonnull : forall p t,
  p <> 0
  -> mtree p t === exists l d r lp rp, [| t = Node l d r |] * p |--> [lp; d; rp]
                                       * mtree lp l * mtree rp r.
Proof.
  heq; cases t; cancel; match goal with
                        | [ H : _ = Node _ _ _ |- _ ] => invert H
                        end; cancel.
Qed.

(** ** Example verification *)

(* As a warm-up to the proof style we suggest for this lab, here's a quick (and
 * silly) example.  Lock #0 owns a tree whose root pointer is stored in address
 * #0.  We don't really care what tree it is, and the thread here loops,
 * repeatedly grafting some arbitrary nonsense onto the tree! *)

Example grow_forever :=
  for _ := tt loop
    _ <- Lock 0;
    root <- Read 0;
    newNode <- Alloc 3;
    _ <- Write newNode root;
    _ <- Write 0 newNode;
    _ <- Unlock 0;
    Return (Again tt)
  done.

(* Lock invariant: address 0 stores the root pointer of some tree. *)
Definition gfinv := (exists p t, 0 |-> p * mtree p t)%sep.

Lemma grow_forever_ok :
  [gfinv] ||- {{emp}} grow_forever {{_ ~> emp}}.
Proof.
  unfold grow_forever, gfinv.
  loop_inv (fun _ : loop_outcome unit => emp)%sep.
  erewrite (mtree_nonnull _ H).
  cancel.
  rewrite mtree_null.
  cancel.
  cancel.
  cancel.
Qed.

(* We can prove the same theorem for a parallel composition of two grower
 * threads. *)
Lemma grows_forever_ok :
  [gfinv] ||- {{emp}} grow_forever || grow_forever {{_ ~> emp}}.
Proof.
  unfold grow_forever, gfinv.
  fork (emp%sep) (emp%sep).
  apply grow_forever_ok.
  apply grow_forever_ok.
  cancel.
  cancel.
Qed.

(* Quick summary of specialized tactics:
 * - [simp]: general simplification
 * - [step]: apply one basic rule of Concurrent Separation Logic.
 * - [ht]: apply as many basic rules of CSL as possible.
 *         (Often it's more pleasant to manually run [step] over and over.
 *          We recommend doing so if [ht] is running for a long time, as [ht]
 *          can get stuck in a loop when it needs your help choosing some
 *          rewrite rules to apply.)
 * - [fork P1 P2]: prove a parallel composition, using [P1] as the precondition
 *                 for the first thread and [P2] for the second.
 * - [loop_inv I]: apply loop rule with this invariant.
 * - [cancel]: prove implications by cancelation.
 * - [setoid_rewrite E]: rewrite with [E] underneath [exists] binders.
 *)


(** ** Your turn! *)

(* Let's prove a program that uses multiple threads to search a tree for a
 * particular data value.  Each thread is looping forever, trying to pop from a
 * shared stack of trees.  If it pops a leaf, it just goes back to looping.  If
 * it pops a node, it checks if the data value matches the "needle" we are
 * searching for in this "haystack."  If so, it sets a flag to indicate that we
 * found the value.  The thread also pushes both children of the node onto the
 * stack, in addition to freeing the memory used for the node, before looping
 * again.  One lock controls the "found it?" flag, and another lock controls the
 * stack of trees. *)

(* This predicate defines linked lists of trees, suitable for the stack. *)
Fixpoint linkedList (p : nat) (ls : list tree) :=
  match ls with
    | nil => [| p = 0 |]
    | t :: ls' => [| p <> 0 |]
                  * exists tp p', p |--> [tp; p'] * mtree tp t * linkedList p' ls'
  end%sep.

(* And here are modified versions of our usual main lemmas about linked
 * lists. *)
Theorem linkedList_null : forall ls,
  linkedList 0 ls === [| ls = nil |].
Proof.
  heq; cases ls; cancel.
Qed.

Theorem linkedList_nonnull : forall p ls,
  p <> 0
  -> linkedList p ls === exists t tp ls' p', [| ls = t :: ls' |] * p |--> [tp; p'] * mtree tp t * linkedList p' ls'.
Proof.
  heq; cases ls; cancel; match goal with
                         | [ H : _ = _ :: _ |- _ ] => invert H
                         end; cancel.
Qed.

Opaque mtree linkedList.

(* Now, here's the code, expanding on the outline from the longish comment
 * above. *)
Example worker needle :=
  for i := tt loop
    _ <- Lock 1;
    head <- Read 1;
    if head ==n 0 then
      _ <- Unlock 1;
      Return (Again tt)
    else
      tp <- Read head;
      tail <- Read (head+1);

      if tp ==n 0 then
        _ <- Write 1 tail;
        _ <- Unlock 1;
        _ <- Free head 2;
        Return (Again tt)
      else
        lp <- Read tp;
        d <- Read (tp+1);
        rp <- Read (tp+1+1);

        ln <- Alloc 2;
        _ <- Write ln lp;
        _ <- Write (ln+1) tail;

        rn <- Alloc 2;
        _ <- Write rn rp;
        _ <- Write (rn+1) ln;

        _ <- Write 1 rn;
        _ <- Unlock 1;

        _ <- Free head 2;
        _ <- Free tp 3;

        if d ==n needle then
          _ <- Lock 0;
          _ <- Write 0 1;
          _ <- Unlock 0;
          Return (Again tt)
        else
          Return (Again tt)
  done.

Example two_workers needle :=
  worker needle || worker needle.

(* To specify this program, we define a predicate for presence of a data value
 * in a tree. *)
Fixpoint inTree (needle : nat) (t : tree) :=
  match t with
  | Leaf => False
  | Node l d r => inTree needle l \/ d = needle \/ inTree needle r
  end.

(* Invariant associated with lock #0: memory address 0 stores a value that may
 * only be 1 if the needle is found in the tree. *)
Definition flag_inv (needle : nat) (t : tree) :=
  (exists b, 0 |-> b * [| b = 1 -> inTree needle t |])%sep.

(* CHALLENGE #1: choose a good invariant for lock #1, concerning the shared
 * stack of trees. *)
Definition stack_inv (needle : nat) (t : tree) := emp%sep.

(* CHALLENGE #2: prove that a single thread obeys the invariants. *)
Lemma worker_ok : forall needle t,
  [flag_inv needle t; stack_inv needle t] ||- {{emp}} worker needle {{_ ~> emp}}.
Proof.
  unfold worker, flag_inv, stack_inv.
  simp.
Admitted.

(* CHALLENGE #3: prove that 2 workers are also OK together. *)
Theorem workers_ok : forall needle t,
  [flag_inv needle t; stack_inv needle t] ||- {{emp}} two_workers needle {{_ ~> emp}}.
Proof.
Admitted.

Fixpoint n_workers (needle n : nat) :=
  match n with
  | O => worker needle
  | S n' => n_workers needle n' || n_workers needle n'
  end.

(* CHALLENGE #4: prove that 2^n workers are also OK. *)
Theorem n_workers_ok : forall needle t n,
  [flag_inv needle t; stack_inv needle t] ||- {{emp}} n_workers needle n {{_ ~> emp}}.
Proof.
Admitted.
