(** * 6.887 Formal Reasoning About Programs - Lab 8
    * Using Hoare Logic *)

Require Import Frap.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)

(** * Using Hoare Logic *)

(* In this lab, we will use the Hoare Logic introduced in class to verify some programs. *)

(* This following definitions are copied from class *)
Inductive exp :=
| Const (n : nat)
| Var (x : string)
| Read (e1 : exp)
| Plus (e1 e2 : exp)
| Minus (e1 e2 : exp)
| Mult (e1 e2 : exp).

Inductive bexp :=
| Equal (e1 e2 : exp)
| Less (e1 e2 : exp).

Definition heap := fmap nat nat.
Definition valuation := fmap var nat.
Definition assertion := heap -> valuation -> Prop.

Inductive cmd :=
| Skip
| Assign (x : var) (e : exp)
| Write (e1 e2 : exp)
| Seq (c1 c2 : cmd)
| If_ (be : bexp) (then_ else_ : cmd)
| While_ (inv : assertion) (be : bexp) (body : cmd)
| Assert (a : assertion).

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).

Fixpoint eval (e : exp) (h : heap) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => v $! x
  | Read e1 => h $! eval e1 h v
  | Plus e1 e2 => eval e1 h v + eval e2 h v
  | Minus e1 e2 => eval e1 h v - eval e2 h v
  | Mult e1 e2 => eval e1 h v * eval e2 h v
  end.

Fixpoint beval (b : bexp) (h : heap) (v : valuation) : bool :=
  match b with
  | Equal e1 e2 => if eval e1 h v ==n eval e2 h v then true else false
  | Less e1 e2 => if eval e2 h v <=? eval e1 h v then false else true
  end.

Inductive exec : heap -> valuation -> cmd -> heap -> valuation -> Prop :=
| ExSkip : forall h v,
  exec h v Skip h v
| ExAssign : forall h v x e,
  exec h v (Assign x e) h (v $+ (x, eval e h v))
| ExWrite : forall h v e1 e2,
  exec h v (Write e1 e2) (h $+ (eval e1 h v, eval e2 h v)) v
| ExSeq : forall h1 v1 c1 h2 v2 c2 h3 v3,
  exec h1 v1 c1 h2 v2
  -> exec h2 v2 c2 h3 v3
  -> exec h1 v1 (Seq c1 c2) h3 v3
| ExIfTrue : forall h1 v1 b c1 c2 h2 v2,
  beval b h1 v1 = true
  -> exec h1 v1 c1 h2 v2
  -> exec h1 v1 (If_ b c1 c2) h2 v2
| ExIfFalse : forall h1 v1 b c1 c2 h2 v2,
  beval b h1 v1 = false
  -> exec h1 v1 c2 h2 v2
  -> exec h1 v1 (If_ b c1 c2) h2 v2
| ExWhileFalse : forall I h v b c,
  beval b h v = false
  -> exec h v (While_ I b c) h v
| ExWhileTrue : forall I h1 v1 b c h2 v2 h3 v3,
  beval b h1 v1 = true
  -> exec h1 v1 c h2 v2
  -> exec h2 v2 (While_ I b c) h3 v3
  -> exec h1 v1 (While_ I b c) h3 v3
| ExAssert : forall h v (a : assertion),
  a h v
  -> exec h v (Assert a) h v.

Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
| HtSkip : forall P, hoare_triple P Skip P
| HtAssign : forall (P : assertion) x e,
  hoare_triple P (Assign x e) (fun h v => exists v', P h v' /\ v = v' $+ (x, eval e h v'))
| HtWrite : forall (P : assertion) (e1 e2 : exp),
  hoare_triple P (Write e1 e2) (fun h v => exists h', P h' v /\ h = h' $+ (eval e1 h' v, eval e2 h' v))
| HtSeq : forall (P Q R : assertion) c1 c2,
  hoare_triple P c1 Q
  -> hoare_triple Q c2 R
  -> hoare_triple P (Seq c1 c2) R
| HtIf : forall (P Q1 Q2 : assertion) b c1 c2,
  hoare_triple (fun h v => P h v /\ beval b h v = true) c1 Q1
  -> hoare_triple (fun h v => P h v /\ beval b h v = false) c2 Q2
  -> hoare_triple P (If_ b c1 c2) (fun h v => Q1 h v \/ Q2 h v)
| HtWhile : forall (I P : assertion) b c,
  (forall h v, P h v -> I h v)
  -> hoare_triple (fun h v => I h v /\ beval b h v = true) c I
  -> hoare_triple P (While_ I b c) (fun h v => I h v /\ beval b h v = false)
| HtAssert : forall P I : assertion,
  (forall h v, P h v -> I h v)
  -> hoare_triple P (Assert I) P
| HtConsequence : forall (P Q P' Q' : assertion) c,
  hoare_triple P c Q
  -> (forall h v, P' h v -> P h v)
  -> (forall h v, Q h v -> Q' h v)
  -> hoare_triple P' c Q'.

Coercion Const : nat >-> exp.
Coercion Var : string >-> exp.
Notation "*[ e ]" := (Read e) : cmd_scope.
Infix "+" := Plus : cmd_scope.
Infix "-" := Minus : cmd_scope.
Infix "*" := Mult : cmd_scope.
Infix "=" := Equal : cmd_scope.
Infix "<" := Less : cmd_scope.
Definition set (dst src : exp) : cmd :=
  match dst with
  | Read dst' => Write dst' src
  | Var dst' => Assign dst' src
  | _ => Assign "Bad LHS" 0
  end.
Infix "<-" := set (no associativity, at level 70) : cmd_scope.
Infix ";;" := Seq (right associativity, at level 75) : cmd_scope.
Notation "'when' b 'then' then_ 'else' else_ 'done'" := (If_ b then_ else_) (at level 75, e at level 0).
Notation "{{ I }} 'while' b 'loop' body 'done'" := (While_ I b body) (at level 75).
Notation "'assert' {{ I }}" := (Assert I) (at level 75).
Delimit Scope cmd_scope with cmd.

Infix "+" := plus : reset_scope.
Infix "-" := minus : reset_scope.
Infix "*" := mult : reset_scope.
Infix "=" := eq : reset_scope.
Infix "<" := lt : reset_scope.
Delimit Scope reset_scope with reset.
Open Scope reset_scope.

Notation "h & v ~> e" := (fun h v => e%reset) (at level 85, v at level 0).

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c%cmd Q) (at level 90, c at next level).

Lemma HtStrengthenPost : forall (P Q Q' : assertion) c,
  hoare_triple P c Q
  -> (forall h v, Q h v -> Q' h v)
  -> hoare_triple P c Q'.
Proof.
  simplify; eapply HtConsequence; eauto.
Qed.

Ltac ht1 := apply HtSkip || apply HtAssign || apply HtWrite || eapply HtSeq
            || eapply HtIf || eapply HtWhile || eapply HtAssert
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

Inductive step : heap * valuation * cmd -> heap * valuation * cmd -> Prop :=
| StAssign : forall h v x e,
  step (h, v, Assign x e) (h, v $+ (x, eval e h v), Skip)
| StWrite : forall h v e1 e2,
  step (h, v, Write e1 e2) (h $+ (eval e1 h v, eval e2 h v), v, Skip)
| StStepSkip : forall h v c,
  step (h, v, Seq Skip c) (h, v, c)
| StStepRec : forall h1 v1 c1 h2 v2 c1' c2,
  step (h1, v1, c1) (h2, v2, c1')
  -> step (h1, v1, Seq c1 c2) (h2, v2, Seq c1' c2)
| StIfTrue : forall h v b c1 c2,
  beval b h v = true
  -> step (h, v, If_ b c1 c2) (h, v, c1)
| StIfFalse : forall h v b c1 c2,
  beval b h v = false
  -> step (h, v, If_ b c1 c2) (h, v, c2)
| StWhileFalse : forall I h v b c,
  beval b h v = false
  -> step (h, v, While_ I b c) (h, v, Skip)
| StWhileTrue : forall I h v b c,
  beval b h v = true
  -> step (h, v, While_ I b c) (h, v, Seq c (While_ I b c))
| StAssert : forall h v (a : assertion),
  a h v
  -> step (h, v, Assert a) (h, v, Skip).

Hint Constructors step.

Definition trsys_of (st : heap * valuation * cmd) := {|
  Initial := {st};
  Step := step
|}.

Definition unstuck (st : heap * valuation * cmd) :=
  snd st = Skip
  \/ exists st', step st st'.

Lemma hoare_triple_unstuck : forall P c Q,
  {{P}} c {{Q}}
  -> forall h v, P h v
                 -> unstuck (h, v, c).
Proof.
  induct 1; unfold unstuck; simplify; propositional; eauto.

  apply IHhoare_triple1 in H1.
  unfold unstuck in H1; simplify; first_order; subst; eauto.
  cases x.
  cases p.
  eauto.

  cases (beval b h v); eauto.

  cases (beval b h v); eauto.

  apply H0 in H2.
  apply IHhoare_triple in H2.
  unfold unstuck in H2; simplify; first_order.
Qed.

Lemma hoare_triple_Skip : forall P Q,
  {{P}} Skip {{Q}}
  -> forall h v, P h v -> Q h v.
Proof.
  induct 1; auto.
Qed.

Lemma hoare_triple_step : forall P c Q,
  {{P}} c {{Q}}
  -> forall h v h' v' c',
      step (h, v, c) (h', v', c')
      -> P h v
      -> {{h''&v'' ~> h'' = h' /\ v'' = v'}} c' {{Q}}.
Proof.
  induct 1.

  invert 1.

  invert 1; ht; eauto.

  invert 1; ht; eauto.

  invert 1; simplify.

  eapply HtConsequence; eauto.
  propositional; subst.
  eapply hoare_triple_Skip; eauto.

  econstructor; eauto.

  invert 1; simplify.
  eapply HtConsequence; eauto; equality.
  eapply HtConsequence; eauto; equality.

  invert 1; simplify.
  eapply HtConsequence with (P := h'' & v'' ~> h'' = h' /\ v'' = v').
  apply HtSkip.
  auto.
  simplify; propositional; subst; eauto.

  econstructor.
  eapply HtConsequence; eauto.
  simplify; propositional; subst; eauto.
  econstructor; eauto.

  invert 1; simplify.
  eapply HtConsequence; eauto.
  econstructor.
  simplify; propositional; subst; eauto.

  simplify.
  eapply HtConsequence.
  eapply IHhoare_triple; eauto.
  simplify; propositional; subst; eauto.
  auto.
Qed.

Theorem hoare_triple_invariant : forall P c Q h v,
  {{P}} c {{Q}}
  -> P h v
  -> invariantFor (trsys_of (h, v, c)) unstuck.
Proof.
  simplify.
  apply invariant_weaken with (invariant1 := fun st => {{h&v ~> h = fst (fst st)
                                                           /\ v = snd (fst st)}}
                                                         snd st
                                                       {{_&_ ~> True}}).

  apply invariant_induction; simplify.

  propositional; subst; simplify.
  eapply HtConsequence; eauto.
  equality.

  cases s.
  cases s'.
  cases p.
  cases p0.
  simplify.
  eapply hoare_triple_step; eauto.
  simplify; auto.

  simplify.
  cases s.
  cases p.
  simplify.
  eapply hoare_triple_unstuck; eauto.
  simplify; auto.
Qed.

(** * Challenge 1: Infinite loop *)

(* We mentioned this nonterminating program in class.  Now your task is to prove
 * that it won't get stuck during execution, possibly using the
 * [hoare_triple_invariant] theorem. *)

Definition forever := (
  "i" <- 1;;
  "n" <- 1;;
  {{h&v ~> v $! "i" > 0}}
  while 0 < "i" loop
    "i" <- "i" * 2;;
    "n" <- "n" + "i";;
    assert {{h&v ~> v $! "n" >= 1}}
  done;;

  assert {{_&_ ~> False}}
  (* Note that this last assertion implies that the program never terminates! *)
)%cmd.

Theorem forever_invariant : invariantFor (trsys_of ($0, $0, forever)) unstuck.
Proof.
Admitted.


(* Some hint preparation for the following challenges *)

(* One simple lemma turns out to be helpful to guide [eauto] properly. *)
Lemma leq_f : forall A (m : fmap A nat) x y,
  x = y
  -> m $! x <= m $! y.
Proof.
  ht.
Qed.

Hint Resolve leq_f.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic.
Hint Extern 1 (_ < _) => linear_arithmetic.
Hint Extern 1 (_ <= _) => linear_arithmetic.
(* We also register [linear_arithmetic] as a step to try during proof search. *)


(** * Challenge 2: Max of array *)

(* Verify the following 'max of array' program.  See the final postcondition for
 * how we interpret a part of memory as an array.  You can change loop-invariant
 * annotations in the program to facilitate your verification. *)

Theorem maxOfArray_ok :
  {{_&_ ~> True}}
    "max" <- *["a"];;
    "i" <- 0;;
    {{h&v ~> True }}
    while "i" < "n" loop
      when "max" < *["a" + "i"] then
        "max" <- *["a" + "i"]
      else
        Skip
      done;;
      "i" <- "i" + 1
    done
  {{h&v ~> forall i, i < v $! "n" -> h $! (v $! "a" + i) <= v $! "max"}}.
Proof.
Admitted.


(** * Challenge 3: Selection sort *)

(* Verify the following 'selection sort' program. Note that we only prove here
 * that the final array is sorted, *not* that it's a permutation of the original
 * array. *)

Theorem selectionSort_ok :
  {{_&_ ~> True}}
    "i" <- 0;;
    {{h&v ~> True }}
    while "i" < "n" loop
      "j" <- "i"+1;;
      "best" <- "i";;
      {{h&v ~> True }}
      while "j" < "n" loop
        when *["a" + "j"] < *["a" + "best"] then
          "best" <- "j"
        else
          Skip
        done;;
        "j" <- "j" + 1
      done;;
      "tmp" <- *["a" + "best"];;
      *["a" + "best"] <- *["a" + "i"];;
      *["a" + "i"] <- "tmp";;
      "i" <- "i" + 1
    done
  {{h&v ~> forall i j, i < j < v $! "n" -> h $! (v $! "a" + i) <= h $! (v $! "a" + j)}}.
Proof.
Admitted.
