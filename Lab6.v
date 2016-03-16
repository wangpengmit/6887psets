(** * 6.887 Formal Reasoning About Programs - Lab 6
    * Type Systems *)

Require Import Frap.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)

Set Implicit Arguments.

(** * Simply typed lambda calculus with extras: product types and sum types *)

(* In this challenge, we add pairs and disjoint unions to the simply typed
 * lambda calculus from the lecture. Their types are called product types and
 * sum types correspondingly. *)

Module ProductSum.
  
  (* Expression syntax *)
  Inductive exp :=
  | Var (x : var)
  | Const (n : nat)
  | Plus (e1 e2 : exp)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)
  (* New stuff from here *)
  | Pair (e1 e2 : exp)
  (* [Pair e1 e2] is how we construct a new pair, by putting two expressions
   * together as the two components. *)
  | Fst (e1 : exp)
  | Snd (e1 : exp)
  (* These are how we use an existing pair, by projecting out its first or
   * second component. *)
  (* For a language feature such as pairs, we sometimes talk about its
   * "introduction forms", which are the syntax used to construct an instance
   * (such as [Pair]); and its "elimination forms", which are the syntax used to
   * pull apart an instance (such as [Fst] and [Snd]). *)
  | Inl (e1 : exp)
  | Inr (e1 : exp)
  (* These are the introduction forms of disjoint unions. *)
  | Match (e : exp) (x1 : var) (e1 : exp) (x2 : var) (e2 : exp)
  (* This is the elimination form of disjoint unions. A disjoint union is an
   * object that could have been constructed by either [Inl] ("left inject")
   * or [Inr] (guess its meaning?). The way to use it is to case-analyse it, and
   * in each case we can access the inner object used to construct the disjoint
   * union. *)
  .
  
  (* Substitution (not capture-avoiding, for the usual reason) *)
  Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
    match e2 with
    | Var y => if y ==v x then e1 else Var y
    | Const n => Const n
    | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
    | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
    | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
    | Pair e2' e2'' => Pair (subst e1 x e2') (subst e1 x e2'')
    | Fst e2' => Fst (subst e1 x e2')
    | Snd e2' => Snd (subst e1 x e2')
    | Inl e2' => Inl (subst e1 x e2')
    | Inr e2' => Inr (subst e1 x e2')
    | Match e2' x1 e2'' x2 e2''' => Match (subst e1 x e2')
                                          x1 (if x1 ==v x then e2'' else subst e1 x e2'')
                                          x2 (if x2 ==v x then e2''' else subst e1 x e2''')
    end.

  (* Values (final results of evaluation) *)
  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1)
  | VPair : forall e1 e2,
      value e1
      -> value e2
      -> value (Pair e1 e2)
  | VInl : forall e1,
      value e1
      -> value (Inl e1)
  | VInr : forall e1,
      value e1
      -> value (Inr e1)
  (* Pairs and disjoint unions are values when their components are all values. *)
  .

  (* Evaluation contexts *)
  Inductive context :=
  | Hole
  | Plus1 (C : context) (e2 : exp)
  | Plus2 (v1 : exp) (C : context)
  | App1 (C : context) (e2 : exp)
  | App2 (v1 : exp) (C : context)
  | Pair1 (C : context) (e2 : exp)
  | Pair2 (v1 : exp) (C : context)
  (* [context] and [plug] rules for pairs will be similar to those for [App]. *)
  | Fst1 (C : context)
  | Snd1 (C : context)
  | Inl1 (C : context)
  | Inr1 (C : context)
  | Match1 (C : context) (x1 : var) (e1 : exp) (x2 : var) (e2 : exp).

  (* Plugging an expression into a context *)
  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugPlus1 : forall e e' C e2,
      plug C e e'
      -> plug (Plus1 C e2) e (Plus e' e2)
  | PlugPlus2 : forall e e' v1 C,
      value v1
      -> plug C e e'
      -> plug (Plus2 v1 C) e (Plus v1 e')
  | PlugApp1 : forall e e' C e2,
      plug C e e'
      -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
      value v1
      -> plug C e e'
      -> plug (App2 v1 C) e (App v1 e')
  | PlugPair1 : forall e e' C e2,
      plug C e e'
      -> plug (Pair1 C e2) e (Pair e' e2)
  | PlugPair2 : forall e e' v1 C,
      value v1
      -> plug C e e'
      -> plug (Pair2 v1 C) e (Pair v1 e')
  (* Evaluate the first component of a pair to a value, then evaluate the second
   * component. *)
  | PlugFst1 : forall e e' C,
      plug C e e'
      -> plug (Fst1 C) e (Fst e')
  | PlugSnd1 : forall e e' C,
      plug C e e'
      -> plug (Snd1 C) e (Snd e')
  | PlugInl1 : forall e e' C,
      plug C e e'
      -> plug (Inl1 C) e (Inl e')
  | PlugInr1 : forall e e' C,
      plug C e e'
      -> plug (Inr1 C) e (Inr e')
  | PlugMatch1 : forall e e' C x1 e1 x2 e2,
      plug C e e'
      -> plug (Match1 C x1 e1 x2 e2) e (Match e' x1 e1 x2 e2)
  (* Evaluate the discriminee (thing being matched on) to a value, which should
   * be in the form of either [Inl _] or [Inr _]). The actual matching will be
   * done by the following [step0] relation. *)
  .

  (* Small-step, call-by-value evaluation *)
  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
      value v
      -> step0 (App (Abs x e) v) (subst v x e)
  | Add : forall n1 n2,
      step0 (Plus (Const n1) (Const n2)) (Const (n1 + n2))
  | GetFst : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Fst (Pair v1 v2)) v1
  | GetSnd : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Snd (Pair v1 v2)) v2
  (* Constructor and eliminator "cancel" each other. *)
  | MatchInl : forall v x1 e1 x2 e2,
      value v 
      -> step0 (Match (Inl v) x1 e1 x2 e2) (subst v x1 e1)
  | MatchInr : forall v x1 e1 x2 e2,
      value v
      -> step0 (Match (Inr v) x1 e1 x2 e2) (subst v x2 e2)
  (* Choose a branch according to the discriminee's value form and replace the
   * variable in the chosen branch with the actual inner component of the
   * discriminee. *)
  .
  
  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
      plug C e1 e1'
      -> plug C e2 e2'
      -> step0 e1 e2
      -> step e1' e2'.

  Definition trsys_of (e : exp) := {|
    Initial := {e};
    Step := step
  |}.

  (* Syntax of types *)
  Inductive type :=
  | Nat
  | Fun (dom ran : type)
  | Prod (t1 t2 : type)
  (* Product types for pairs *)
  | Sum (t1 t2 : type)
  (* Sum types for disjoint unions *)
  .

  (* Expression typing relation *)
  Inductive hasty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
      G $? x = Some t
      -> hasty G (Var x) t
  | HtConst : forall G n,
      hasty G (Const n) Nat
  | HtPlus : forall G e1 e2,
      hasty G e1 Nat
      -> hasty G e2 Nat
      -> hasty G (Plus e1 e2) Nat
  | HtAbs : forall G x e1 t1 t2,
      hasty (G $+ (x, t1)) e1 t2
      -> hasty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
      hasty G e1 (Fun t1 t2)
      -> hasty G e2 t1
      -> hasty G (App e1 e2) t2
  (* CHALLENGE #1: Fill in the rest of the typing rules here, translated from
   * what's written on the blackboard. *)
  .

  Hint Constructors value plug step0 step hasty.

  (* BEGIN some automation magic. The [t] tactic will be handy for you. *)

  Ltac with12 t := (t; []) || (t; [|]).

  Ltac t0 := match goal with
             | [ H : ex _ |- _ ] => invert H
             | [ H : _ /\ _ |- _ ] => invert H
             | [ |- context[_ $+ (?x, _) $? ?y] ] => cases (x ==v y); simplify
             | [ |- context[?x ==v ?y] ] => cases (x ==v y); simplify

             | [ H : step _ _ |- _ ] => invert H
             | [ H : step0 _ _ |- _ ] => invert1 H
             | [ H : hasty _ ?e _, H' : value ?e |- _ ] => with12 ltac:(invert H'; invert H)
             | [ H : hasty _ _ _ |- _ ] => invert2 H
             | [ H : plug _ _ _ |- _ ] => invert1 H
             | [ H : Some _ = Some _ |- _ ] => invert H
             end; subst.

  Ltac t := simplify; subst; propositional; repeat (t0; simplify); try equality.

  (* END automation magic. Don't forget to try the [t] tactic;) *)

  (* CHALLENGE #2: Prove the safety ("unstuckness") of any well-typed
   * expression. *)
  Theorem safety : forall e t, hasty $0 e t
                               -> invariantFor (trsys_of e)
                                               (fun e' => value e'
                                                          \/ exists e'', step e' e'').
  Proof.
  Admitted.
  
End ProductSum.

(** *Extra extras:  Lists and General Recursions *)

(* In this challenge we will add even more goodies to lambda calculus (yes, a
 * large piece of PL research is adding goodies to lambda calculus).  Lists
 * could be useful, according to our Coq experience. General recursion could
 * also be useful, according to our C experience, and our Coq experience having
 * to work around not having it.  It turns out that in simply typed lambda
 * calculus, every expression terminates, so in order to have general recursion
 * that can run forever, we need to explicitly add it to the
 * language/calculus. *)

Module ListFixpoint.
  
  (* Expression syntax *)
  Inductive exp :=
  | Var (x : var)
  | UnitExp (* We include this extra value, as the sole inhabitant of the unit
             * type.  If we don't include some *base type* like unit, only
             * including function and list types, then we can *prove* that no
             * types exist!  (That would be a fun exercise for the reader.) *)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)
  (* New stuff from here *)
  | Fix (x : var) (e : exp)
  (* General recursion ("fixpoints"). 
   * The evaluation rule for a fixpoint [fix x => e] is that it will always
   * (unconditionally) "unwinds" to [ [(fix x => e)/x] e ], that is, replacing
   * variable [x] with the whole fixpoint itself in the body [e]. *)
  | Nil
  | Cons (e1 e2 : exp)
  | Match (e : exp) (e1 : exp) (hd tl : var) (e2 : exp)
  (* Introduction and elimination forms for lists. Read [Match e e1 x1 x2 e2]
   * as "match e with | Nil => e1 | Cons x1 x2 => e2 end". *)
  .
  
  (* Substitution (not capture-avoiding, for the usual reason) *)
  Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
    match e2 with
    | Var y => if y ==v x then e1 else Var y
    | UnitExp => UnitExp
    | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
    | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
    | Fix y e2' => Fix y (if y ==v x then e2' else subst e1 x e2')
    | Nil => Nil
    | Cons e2' e2'' => Cons (subst e1 x e2') (subst e1 x e2'')
    | Match e2' e2'' x1 x2 e2''' =>
      Match (subst e1 x e2') (subst e1 x e2'')
            x1 x2 (if x1 ==v x then e2''' else if x2 ==v x then e2''' else subst e1 x e2''')
    end.

  (* CHALLENGE #3: augment the following definitions with rules for lists and
   * general recursion, and prove theorem [safety]. *)
  
  (* Values (final results of evaluation) *)
  Inductive value : exp -> Prop :=
  | VUnit : value UnitExp
  | VAbs : forall x e1, value (Abs x e1)
  .

  (* Evaluation contexts *)
  Inductive context :=
  | Hole
  | App1 (C : context) (e2 : exp)
  | App2 (v1 : exp) (C : context)
  .

  (* Plugging an expression into a context *)
  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugApp1 : forall e e' C e2,
      plug C e e'
      -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
      value v1
      -> plug C e e'
      -> plug (App2 v1 C) e (App v1 e')
  .

  (* Small-step, call-by-value evaluation *)
  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
      value v ->
      step0 (App (Abs x e) v) (subst v x e)
  .
  
  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
      plug C e1 e1'
      -> plug C e2 e2'
      -> step0 e1 e2
      -> step e1' e2'.

  Definition trsys_of (e : exp) := {|
    Initial := {e};
    Step := step
  |}.

  (* Syntax of types *)
  Inductive type :=
  | Unit
  | Fun (dom ran : type)
  .

  (* Expression typing relation *)
  Inductive hasty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
      G $? x = Some t
      -> hasty G (Var x) t
  | HtAbs : forall G x e1 t1 t2,
      hasty (G $+ (x, t1)) e1 t2
      -> hasty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
      hasty G e1 (Fun t1 t2)
      -> hasty G e2 t1
      -> hasty G (App e1 e2) t2
  .

  Hint Constructors value plug step0 step hasty.

  Ltac with12 t := (t; []) || (t; [|]).

  (* Here's the tactic from before, which is probably going to fail dramatically
   * in at least one case of the expanded proof! *)
  Ltac t0 := match goal with
             | [ H : ex _ |- _ ] => invert H
             | [ H : _ /\ _ |- _ ] => invert H
             | [ |- context[_ $+ (?x, _) $? ?y] ] => cases (x ==v y); simplify
             | [ |- context[?x ==v ?y] ] => cases (x ==v y); simplify

             | [ H : step _ _ |- _ ] => invert H
             | [ H : step0 _ _ |- _ ] => invert1 H
             | [ H : hasty _ ?e _, H' : value ?e |- _ ] => with12 ltac:(invert H'; invert H)
             | [ H : hasty _ _ _ |- _ ] => invert2 H
             | [ H : plug _ _ _ |- _ ] => invert1 H
             | [ H : Some _ = Some _ |- _ ] => invert H
             end; subst.

  Ltac t := simplify; subst; propositional; repeat (t0; simplify); try equality.
  
  (* Coq Hint: If Coq displays the message "No more subgoals but
   * non-instantiated existential variables" before [Qed], it means there remain
   * some existential variables whose values do not matter for the proof, but
   * you still have to pick values for them.  Use the command
   * [Grab Existential Variables.] to convert these existential variables into
   * subgoals, which you can then "solve" using the [exact E] tactic, to give a
   * term of the requested type. *)
  
  Theorem safety : forall e t, hasty $0 e t
                          -> invariantFor (trsys_of e)
                                         (fun e' => value e'
                                                 \/ exists e'', step e' e'').
  Proof.
  Admitted.
  
End ListFixpoint.
