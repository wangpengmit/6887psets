(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 5 *)

Require Import Frap.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)

Set Implicit Arguments.

(** * Universal polymorphism *)

(* In this problem set you will be asked to add universal polymorphism to
 * simply typed lambda calculus.  Universal polymorphism is the formal concept
 * underneath C++'s templates and Java's generics.  The idea is to let something
 * (a function, a class, etc.) be usable with different types.  For example,
 * instead of having a length function with type [list Nat -> Nat] for lists of
 * natural numbers and another one with type [list String -> Nat] for lists of
 * strings, we can have a single length function [length] with type
 * [\forall X. list X -> Nat].  Here [X] is a *type variable*, standing for an
 * abitrary type that will be given later.  [length] is defined as
 * [\\X. \ls : list X. ...].  The [\\X. _] part is called a *type abstraction*,
 * saying that this term is type-generic with regard to type [X]. To specialize
 * [length] for lists of natural numbers, we explicitly write [length [Nat] ],
 * which is called a specialization or *type application*.  A type of the form
 * [\forall X. _] is called a universal type.
 * 
 * In summary, to add universal polymorphism, we need to add three things to the
 * language: 
 * (1) universal types (the type for type-generic terms): [\forall X. t] 
 * (2) type abstraction (the introduction form for type-generic terms): [\\X. e]
 * (3) type application (the elimination form): [e [t] ].
 *
 * The word "polymorphism" in the functional-programming community means using
 * universal types to write type-generic code, hence the name "universal
 * polymorphism."  The kind of "polymorphism" used in the OOP community, dealing
 * with late binding and dynamic dispatch, is called "ad-hoc polymorphism".
 *)

(* Syntax of types *)
Inductive type :=
| Nat
| Fun (dom ran : type)
(* new stuff from here *)
| VarT (a : var)
(* A type could be a type variable, introduced somewhere else. *)
| Universal (a : var) (t : type)
(* Universal type [\forall X. t] *)
.

(* Expression syntax *)
Inductive exp :=
| Var (x : var)
| Const (n : nat)
| Plus (e1 e2 : exp)
| Abs (x : var) (e1 : exp)
| App (e1 e2 : exp)
(* new stuff from here *)
| AbsT (x : var) (e1 : exp)
(* Type abstraction [\\X. e] *)
| AppT (e1 : exp) (t : type)
(* Type application [e [t] ] *)
.

(* Values (final results of evaluation) *)
Inductive value : exp -> Prop :=
| VConst : forall n, value (Const n)
| VAbs : forall x e1, value (Abs x e1)
| VAbsT : forall x e, value (AbsT x e)
(* Type abstraction is also a value. *)
.

(* Substitution (not capture-avoiding, for the usual reason) *)
Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
  match e2 with
  | Var y => if y ==v x then e1 else Var y
  | Const n => Const n
  | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
  | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
  | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
  | AbsT y e2' => AbsT y (subst e1 x e2') (* type variables and term variables are in different namespaces, so it doesn't matter whether y = x here *)
  | AppT e2' t => AppT (subst e1 x e2') t
  end.

(* Substitution of type in type (not capture-avoiding, for the usual reason) *)
Fixpoint subst_t_t (t1 : type) (x : var) (t2 : type) : type :=
  match t2 with
  | Nat => Nat
  | Fun t2' t2'' => Fun (subst_t_t t1 x t2') (subst_t_t t1 x t2'')
  | VarT y => if y ==v x then t1 else VarT y
  | Universal y t2' => Universal y (if y ==v x then t2' else subst_t_t t1 x t2')
  end.

(* Substitution of type in exp (not capture-avoiding, for the usual reason) *)
Fixpoint subst_t_e (t1 : type) (x : var) (e2 : exp) : exp :=
  match e2 with
  | Var y => Var y
  | Const n => Const n
  | Plus e2' e2'' => Plus (subst_t_e t1 x e2') (subst_t_e t1 x e2'')
  | Abs y e2' => Abs y (subst_t_e t1 x e2')
  | App e2' e2'' => App (subst_t_e t1 x e2') (subst_t_e t1 x e2'')
  | AbsT y e2' => AbsT y (if y ==v x then e2' else subst_t_e t1 x e2')
  | AppT e2' t2' => AppT (subst_t_e t1 x e2') (subst_t_t t1 x t2')
  end.

(* Evaluation contexts *)
Inductive context :=
| Hole
| Plus1 (C : context) (e2 : exp)
| Plus2 (v1 : exp) (C : context)
| App1 (C : context) (e2 : exp)
| App2 (v1 : exp) (C : context)
| CtxAppT (C : context) (t : type)
.

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
| PlugAppT : forall e e' C t,
    plug C e e' ->
    plug (CtxAppT C t) e (AppT e' t)
(* Evaluate the type-generic term to a value before subsituting for type. *)
.

(* Small-step, call-by-value evaluation *)
Inductive step0 : exp -> exp -> Prop :=
| Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)
| Add : forall n1 n2,
    step0 (Plus (Const n1) (Const n2)) (Const (n1 + n2))
| BetaT : forall x e t,
    step0 (AppT (AbsT x e) t) (subst_t_e t x e)
(* Replace formal type argument [x] with actual type [t]. *)
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

(* Type well-formedness *)
(* Because now we have the ability to write nonsense types (e.g. by misspelling
 * type variables), we need to define what types are well-formed.  This
 * definition also takes in a set of variable names to be the set of visible
 * type variables, called a type-variable context or kinding context.
 * We use [fmap var unit] as [set var], to avoid reasoning about both [fmap] and
 * [set], to keep things simple.  Notice, then, the similarities with the
 * original typing judgment for simply typed lambda calculus.  The difference
 * here is that type variables don't have their own "types"; they're just
 * in-scope or not! *)
Inductive wfty : fmap var unit -> type -> Prop :=
| WfNat : forall L,
    wfty L Nat
| WfFun : forall L t1 t2,
    wfty L t1 ->
    wfty L t2 ->
    wfty L (Fun t1 t2)
| WfVarT : forall L x,
    L $? x = Some tt ->
    wfty L (VarT x)
| WfUniversal : forall L x t,
    wfty (L $+ (x, tt)) t ->
    wfty L (Universal x t)
.

(* Expression typing relation *)
(* Now the typing relation also needs to take in a kinding context as
 * argument. *)
Inductive hasty : fmap var unit -> fmap var type -> exp -> type -> Prop :=
| HtVar : forall L G x t,
    G $? x = Some t 
    -> wfty L t (* Need to make sure [t] is well-formed. *)
    -> hasty L G (Var x) t
| HtConst : forall L G n,
    hasty L G (Const n) Nat
| HtPlus : forall L G e1 e2,
    hasty L G e1 Nat
    -> hasty L G e2 Nat
    -> hasty L G (Plus e1 e2) Nat
| HtAbs : forall L G x e1 t1 t2,
    hasty L (G $+ (x, t1)) e1 t2
    -> hasty L G (Abs x e1) (Fun t1 t2)
| HtApp : forall L G e1 e2 t1 t2,
    hasty L G e1 (Fun t1 t2)
    -> hasty L G e2 t1
    -> hasty L G (App e1 e2) t2
| HtAbsT : forall L G x e t,
    (* To avoid capturing type variables in the typing context, we empty out
     * the latter!  This is a restriction of the expressiveness of the language
     * due to our simplistic treatment of [subst].  We can think of this
     * restriction as saying that polymorphism is only allowed at the beginning
     * of a top-level function definition, rather than nested within terms at
     * arbitrary positions. *)
    hasty (L $+ (x, tt)) $0 e t
    -> hasty L G (AbsT x e) (Universal x t)
| HtAppT : forall L G e x t1 t2 t,
    hasty L G e (Universal x t1)
    (* Our non-capture-avoiding subsitution is only sound when [t2] is a
     * closed type. *)
    -> wfty $0 t2 (* Need to make sure [t2] is well-formed. *)
    -> t = subst_t_t t2 x t1
    -> hasty L G (AppT e t2) t
.

Hint Constructors value plug step0 step wfty hasty.

(* BEGIN some automation magic. The [t] tactic will be handy for you. *)

Ltac with12 t := (t; []) || (t; [|]).

Ltac t0 := match goal with
           | [ H : ex _ |- _ ] => invert H
           | [ H : _ /\ _ |- _ ] => invert H
           | [ |- context[?x ==v ?y] ] => cases (x ==v y); simplify
           | [ |- context[_ $+ (?x, _) $? ?y] ] => cases (x ==v y); simplify
           | [ H : step _ _ |- _ ] => invert H
           | [ H : step0 _ _ |- _ ] => invert1 H
           | [ H : hasty _ _ ?e _, H' : value ?e |- _ ] => with12 ltac:(invert H'; invert H)
           | [ H : hasty _ _ _ _ |- _ ] => invert2 H
           | [ H : plug _ _ _ |- _ ] => invert1 H
           | [ H : Some _ = Some _ |- _ ] => invert H
           | [ H : wfty _ _ |- _ ] => invert2 H
           end; subst.

Ltac t := simplify; subst; propositional; repeat (t0; simplify); try equality.

(* End automation magic. Don't forget to try the [t] tactic. *)

(* Some lemmas to guide automation *)

Lemma weakening_override : forall V G G' (x : var) (t : V),
    (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
    -> (forall x' t', G $+ (x, t) $? x' = Some t'
                -> G' $+ (x, t) $? x' = Some t').
Proof.
  t; eauto.
Qed.

Hint Resolve weakening_override.

(* Replacing a typing context with an equal one has no effect (useful to guide
 * proof search). *)
Lemma hasty_change : forall L G e t,
    hasty L G e t
    -> forall G', G' = G
            -> hasty L G' e t.
Proof.
  t.
Qed.

Hint Resolve hasty_change.

(* The counterpart of [hasty_change] for type variables *)
Lemma hasty_change_t : forall L G e t,
    hasty L G e t
    -> forall L', L' = L
            -> hasty L' G e t.
Proof.
  t.
Qed.

Hint Resolve hasty_change_t.

Module Type S.

  (* We provide you some lemma statements as a roadmap for the final theorem. *)

  (* Raising a typing derivation to a larger typing context *)
  Axiom weakening : forall L G e t,
    hasty L G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
                  -> hasty L G' e t.

  (* The counterpart of [weakening] for [wfty] *)
  Axiom weakening_wfty : forall L t,
      wfty L t
      -> forall L', (forall x t, L $? x = Some t -> L' $? x = Some t)
                    -> wfty L' t.

  (* The counterpart of [weakening] for type variables *)
  Axiom weakening_t : forall L G e t,
      hasty L G e t
      -> forall L', (forall x t, L $? x = Some t -> L' $? x = Some t)
                    -> hasty L' G e t.

  (* Replacing a variable with a properly typed term preserves typing. *)
  Axiom substitution : forall L G x t' e t e',
      hasty L (G $+ (x, t')) e t
      -> hasty $0 $0 e' t'
      -> hasty L G (subst e' x e) t.

  (* Replacing a type variable with a well-formed type preserves typing. *)
  Axiom substitution_t_e : forall L G x e t t',
      hasty (L $+ (x, tt)) G e t
      -> wfty $0 t'
      (* G' is a supermap of [fmap_map (subst_t_t t' x) G], where [fmap_map f m] means
       * apply [f] to every domain value in [m].  [fmap_map] is not defined in [Frap],
       * so we use this Prop-y version. *)
      -> forall G',
          (forall y t, G $? y = Some t -> G' $? y = Some (subst_t_t t' x t)) ->
          hasty L G' (subst_t_e t' x e) (subst_t_t t' x t).

  (* This is the final safety theorem we really want. *)
  Axiom safety : forall e t, hasty $0 $0 e t
                             -> invariantFor (trsys_of e)
                                             (fun e' => value e'
                                                        \/ exists e'', step e' e'').

End S.
