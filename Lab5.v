(** * 6.887 Formal Reasoning About Programs - Lab 4
    * Abstract Interpretation *)

Require Import Frap Imp.

(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)

Set Implicit Arguments.


(* In lecture, we saw a very general abstract-interpretation framework, but it
 * had one important weakness (among others): it always ignores conditional
 * expressions, so we get significant imprecision in modeling "if" and "while."
 * This lab is all about
 * (1) extending the framework to analyze conditionals;
 * (2) extending the example even-odd interpretation for the new framework; and
 * (3) verifying a particular program automatically, where the old framework
 *     would fail because of precision loss. *)

(* FIRST, here's our old definition of an abstract interpretation.  In fact,
 * this fill is an already-compiling excerpt of the code from lecture, with some
 * comments indicating changes that we'd like you to make.  Your highly
 * strenuous first task is to uncomment the *two new record fields* below, which
 * provide the extra information for sound abstract interpretation of
 * conditionals. *)
Record absint := {
  Domain :> Set;
  (* We will represent concrete values (natural numbers) with this alternative,
   * abstract set.  This [:>] notation lets us treat any [absint] as its
   * [Domain], automatically.  See below for examples (e.g., return type of
   * [absint_interp]). *)
  Top : Domain;
  (* A universal (least informative) element, describing *all* concrete
   * values *)
  Constant : nat -> Domain;
  (* Most accurate representation of a constant *)
  Add : Domain -> Domain -> Domain;
  Subtract : Domain -> Domain -> Domain;
  Multiply : Domain -> Domain -> Domain;
  (* Abstract versions of arithmetic operators *)
  Join : Domain -> Domain -> Domain;
  (* Returns some new element that covers all cases of each of its inputs *)
  Represents : nat -> Domain -> Prop
  (* Which elements represent which numbers? *)

  (* UNCOMMENT THIS PART TO START THE LAB! *)
(*;
  (* Given our knowledge of a value, could it possibly be zero or nonzero? *)
  CouldBeZero : Domain -> bool;
  CouldBeNonzero : Domain -> bool
*)
}.

(* CHALLENGE #1: Add new algebraic laws to this soundness condition, sufficient
 * to enable you to prove the theorems from later challenges.  You may find
 * yourself returning here frequently as you work on those proofs, when you find
 * you need a new law! *)
Record absint_sound (a : absint) : Prop := {
  TopSound : forall n, a.(Represents) n a.(Top);

  ConstSound : forall n, a.(Represents) n (a.(Constant) n);

  AddSound : forall n na m ma, a.(Represents) n na
                               -> a.(Represents) m ma
                               -> a.(Represents) (n + m) (a.(Add) na ma);
  SubtractSound: forall n na m ma, a.(Represents) n na
                                   -> a.(Represents) m ma
                                   -> a.(Represents) (n - m) (a.(Subtract) na ma);
  MultiplySound : forall n na m ma, a.(Represents) n na
                                    -> a.(Represents) m ma
                                    -> a.(Represents) (n * m) (a.(Multiply) na ma);

  AddMonotone : forall na na' ma ma', (forall n, a.(Represents) n na -> a.(Represents) n na')
                                      -> (forall n, a.(Represents) n ma -> a.(Represents) n ma')
                                      -> (forall n, a.(Represents) n (a.(Add) na ma)
                                                    -> a.(Represents) n (a.(Add) na' ma'));
  SubtractMonotone : forall na na' ma ma', (forall n, a.(Represents) n na -> a.(Represents) n na')
                                           -> (forall n, a.(Represents) n ma -> a.(Represents) n ma')
                                           -> (forall n, a.(Represents) n (a.(Subtract) na ma)
                                                         -> a.(Represents) n (a.(Subtract) na' ma'));
  MultiplyMonotone : forall na na' ma ma', (forall n, a.(Represents) n na -> a.(Represents) n na')
                                           -> (forall n, a.(Represents) n ma -> a.(Represents) n ma')
                                           -> (forall n, a.(Represents) n (a.(Multiply) na ma)
                                                         -> a.(Represents) n (a.(Multiply) na' ma'));

  JoinSoundLeft : forall x y n, a.(Represents) n x
                                -> a.(Represents) n (a.(Join) x y);
  JoinSoundRight : forall x y n, a.(Represents) n y
                                 -> a.(Represents) n (a.(Join) x y)
}.

(* Let's ask [eauto] to try all of the above soundness rules automatically. *)
Hint Resolve TopSound ConstSound AddSound SubtractSound MultiplySound
     AddMonotone SubtractMonotone MultiplyMonotone
     JoinSoundLeft JoinSoundRight.


(** * Example: even-odd analysis *)

(* CHALLENGE #2: Extend this even-odd section to work with the new definition.
 * That is, both fill in the new record fields and prove that the extended
 * record is a sound abstract interpretation, starting from the proofs already
 * in place for the old version. *)

Inductive parity := Even | Odd | Either.

Definition isEven (n : nat) := exists k, n = k * 2.
Definition isOdd (n : nat) := exists k, n = k * 2 + 1.

(* BEGIN SPAN OF BORING THEOREMS ABOUT PARITY, WHICH WE WON'T EXPLAIN. *)

Theorem decide_parity : forall n, isEven n \/ isOdd n.
Proof.
  induct n; simplify; propositional.

  left; exists 0; linear_arithmetic.

  invert H.
  right.
  exists x; linear_arithmetic.

  invert H.
  left.
  exists (x + 1); linear_arithmetic.
Qed.

Theorem notEven_odd : forall n, ~isEven n -> isOdd n.
Proof.
  simplify.
  assert (isEven n \/ isOdd n).
  apply decide_parity.
  propositional.
Qed.

Theorem odd_notEven : forall n, isOdd n -> ~isEven n.
Proof.
  propositional.
  invert H.
  invert H0.
  linear_arithmetic.
Qed.

Theorem isEven_0 : isEven 0.
Proof.
  exists 0; linear_arithmetic.
Qed.

Theorem isEven_1 : ~isEven 1.
Proof.
  propositional; invert H; linear_arithmetic.
Qed.

Theorem isEven_S_Even : forall n, isEven n -> ~isEven (S n).
Proof.
  propositional; invert H; invert H0; linear_arithmetic.
Qed.

Theorem isEven_S_Odd : forall n, ~isEven n -> isEven (S n).
Proof.
  propositional.
  apply notEven_odd in H.
  invert H.
  exists (x + 1); linear_arithmetic.
Qed.

Hint Resolve isEven_0 isEven_1 isEven_S_Even isEven_S_Odd.  

(* END SPAN OF BORING THEOREMS ABOUT PARITY. *)

(* Next, we are ready to implement the operators of the abstract
 * interpretation. *)

Definition parity_flip (p : parity) :=
  match p with
  | Even => Odd
  | Odd => Even
  | Either => Either
  end.

Fixpoint parity_const (n : nat) :=
  match n with
  | O => Even
  | S n' => parity_flip (parity_const n')
  end.

Definition parity_add (x y : parity) :=
  match x, y with
  | Even, Even => Even
  | Odd, Odd => Even
  | Even, Odd => Odd
  | Odd, Even => Odd
  | _, _ => Either
  end.

Definition parity_subtract (x y : parity) :=
  match x, y with
  | Even, Even => Even
  | _, _ => Either
  end.
(* Note subtleties with [Either]s above, to deal with underflow at zero! *)

Definition parity_multiply (x y : parity) :=
  match x, y with
  | Even, _ => Even
  | Odd, Odd => Odd
  | _, Even => Even
  | _, _ => Either
  end.

Definition parity_join (x y : parity) :=
  match x, y with
  | Even, Even => Even
  | Odd, Odd => Odd
  | _, _ => Either
  end.

(* What does it mean for a parity to classify a number correctly? *)
Inductive parity_rep : nat -> parity -> Prop :=
| PrEven : forall n,
  isEven n
  -> parity_rep n Even
| PrOdd : forall n,
  ~isEven n
  -> parity_rep n Odd
| PrEither : forall n,
  parity_rep n Either.

Hint Constructors parity_rep.

(* Putting it all together: *)
Definition parity_absint := {|
  Top := Either;
  Constant := parity_const;
  Add := parity_add;
  Subtract := parity_subtract;
  Multiply := parity_multiply;
  Join := parity_join;
  Represents := parity_rep
|}.

(* Now we prove soundness. *)

Lemma parity_const_sound : forall n,
  parity_rep n (parity_const n).
Proof.
  induct n; simplify; eauto.
  cases (parity_const n); simplify; eauto.
  invert IHn; eauto.
  invert IHn; eauto.
Qed.

Hint Resolve parity_const_sound.

Lemma even_not_odd :
  (forall n, parity_rep n Even -> parity_rep n Odd)
  -> False.
Proof.
  simplify.
  specialize (H 0).
  assert (parity_rep 0 Even) by eauto.
  apply H in H0.
  invert H0.
  apply H1.
  auto.
Qed.

Lemma odd_not_even :
  (forall n, parity_rep n Odd -> parity_rep n Even)
  -> False.
Proof.
  simplify.
  specialize (H 1).
  assert (parity_rep 1 Odd) by eauto.
  apply H in H0.
  invert H0.
  invert H1.
  linear_arithmetic.
Qed.

Hint Resolve even_not_odd odd_not_even.

Lemma parity_join_complete : forall n x y,
  parity_rep n (parity_join x y)
  -> parity_rep n x \/ parity_rep n y.
Proof.
  simplify; cases x; cases y; simplify; propositional.
  assert (isEven n \/ isOdd n) by apply decide_parity.
  propositional; eauto using odd_notEven.
  assert (isEven n \/ isOdd n) by apply decide_parity.
  propositional; eauto using odd_notEven.
Qed.

Hint Resolve parity_join_complete.

(* The final proof uses some automation that we won't explain, to descend down
 * to the hearts of the interesting cases. *)

Theorem parity_sound : absint_sound parity_absint.
Proof.
  constructor; simplify; eauto;
  repeat match goal with
         | [ H : parity_rep _ _ |- _ ] => invert H
         | [ H : ~isEven _ |- _ ] => apply notEven_odd in H; invert H
         | [ H : isEven _ |- _ ] => invert H
         | [ p : parity |- _ ] => cases p; simplify; try equality
         end; try solve [ exfalso; eauto ]; try (constructor; try apply odd_notEven).

  (* We finish up by instantiating all those existential quantifiers in uses of
   * [isEven] and [isOdd]. *)
  exists (x0 + x); ring.
  exists (x0 + x); ring.
  exists (x0 + x); ring.
  exists (x0 + x + 1); ring.
  exists (x - x0); linear_arithmetic.
  exists (x * x0 * 2); ring.
  exists ((x * 2 + 1) * x0); ring.
  exists (n * x); ring.
  exists ((x * 2 + 1) * x0); ring.
  exists (2 * x * x0 + x + x0); ring.
  exists (x * m); ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x; ring.
  exists x0; ring.
  exists x0; ring.
Qed.


(** * Interpreting expressions *)

(* Now we're back to the general framework.  Here's an unchanged expression
 * abstract interpreter and its proof.  Feel free to skip ahead to
 * "HERE NEXT." *)

Definition astate (a : absint) := fmap var a.

Fixpoint absint_interp (e : arith) a (s : astate a) : a :=
  match e with
  | Const n => a.(Constant) n
  | Var x => match s $? x with
             | None => a.(Top)
             | Some xa => xa
             end
  | Plus e1 e2 => a.(Add) (absint_interp e1 s) (absint_interp e2 s)
  | Minus e1 e2 => a.(Subtract) (absint_interp e1 s) (absint_interp e2 s)
  | Times e1 e2 => a.(Multiply) (absint_interp e1 s) (absint_interp e2 s)
  end.

Definition merge_astate a : astate a -> astate a -> astate a :=
  merge (fun x y =>
           match x with
           | None => None
           | Some x' =>
             match y with
             | None => None
             | Some y' => Some (a.(Join) x' y')
             end
           end).

Definition subsumed a (s1 s2 : astate a) :=
  forall x, match s1 $? x with
            | None => s2 $? x = None
            | Some xa1 =>
              forall xa2, s2 $? x = Some xa2
                          -> forall n, a.(Represents) n xa1
                                       -> a.(Represents) n xa2
            end.

Theorem subsumed_refl : forall a (s : astate a),
  subsumed s s.
Proof.
  unfold subsumed; simplify.
  cases (s $? x); equality.
Qed.

Hint Resolve subsumed_refl.

Lemma subsumed_use : forall a (s s' : astate a) x n t0 t,
  s $? x = Some t0
  -> subsumed s s'
  -> s' $? x = Some t
  -> Represents a n t0
  -> Represents a n t.
Proof.
  unfold subsumed; simplify.
  specialize (H0 x).
  rewrite H in H0.
  eauto.
Qed.

Lemma subsumed_use_empty : forall a (s s' : astate a) x n t0 t,
  s $? x = None
  -> subsumed s s'
  -> s' $? x = Some t
  -> Represents a n t0
  -> Represents a n t.
Proof.
  unfold subsumed; simplify.
  specialize (H0 x).
  rewrite H in H0.
  equality.
Qed.

Hint Resolve subsumed_use subsumed_use_empty.

Lemma subsumed_trans : forall a (s1 s2 s3 : astate a),
  subsumed s1 s2
  -> subsumed s2 s3
  -> subsumed s1 s3.
Proof.
  unfold subsumed; simplify.
  specialize (H x); specialize (H0 x).
  cases (s1 $? x); simplify.
  cases (s2 $? x); eauto.
  cases (s2 $? x); eauto.
  equality.
Qed.

Lemma subsumed_merge_left : forall a, absint_sound a
  -> forall s1 s2 : astate a,
    subsumed s1 (merge_astate s1 s2).
Proof.
  unfold subsumed, merge_astate; simplify.
  cases (s1 $? x); trivial.
  cases (s2 $? x); simplify; try equality.
  invert H0; eauto.
Qed.

Hint Resolve subsumed_merge_left.

Lemma subsumed_add : forall a, absint_sound a
  -> forall (s1 s2 : astate a) x v1 v2,
  subsumed s1 s2
  -> (forall n, a.(Represents) n v1 -> a.(Represents) n v2)
  -> subsumed (s1 $+ (x, v1)) (s2 $+ (x, v2)).
Proof.
  unfold subsumed; simplify.
  cases (x ==v x0); subst; simplify; eauto.
  invert H2; eauto.
  specialize (H0 x0); eauto.
Qed.

Hint Resolve subsumed_add.

Definition compatible a (s : astate a) (v : valuation) : Prop :=
  forall x xa, s $? x = Some xa
               -> exists n, v $? x = Some n
                            /\ a.(Represents) n xa.

Lemma compatible_add : forall a (s : astate a) v x na n,
  compatible s v
  -> a.(Represents) n na
  -> compatible (s $+ (x, na)) (v $+ (x, n)).
Proof.
  unfold compatible; simplify.
  cases (x ==v x0); simplify; eauto.
  invert H1; eauto.
Qed.

Hint Resolve compatible_add.

Theorem absint_interp_ok : forall a, absint_sound a
  -> forall (s : astate a) v e,
    compatible s v
    -> a.(Represents) (interp e v) (absint_interp e s).
Proof.
  induct e; simplify; eauto.
  cases (s $? x); auto.
  unfold compatible in H0.
  apply H0 in Heq.
  invert Heq.
  propositional.
  rewrite H2.
  assumption.
Qed.

Hint Resolve absint_interp_ok.


(** * Flow-sensitive analysis *)

Definition astates (a : absint) := fmap cmd (astate a).

(* HERE NEXT!  CHALLENGE #2: Extend the old command stepper to model
 * conditionals more precisely. *)

Fixpoint absint_step a (s : astate a) (c : cmd) (wrap : cmd -> cmd) : option (astates a) :=
  match c with
  | Skip => None
  | Assign x e => Some ($0 $+ (wrap Skip, s $+ (x, absint_interp e s)))
  | Sequence c1 c2 =>
    match absint_step s c1 (fun c => wrap (Sequence c c2)) with
    | None => Some ($0 $+ (wrap c2, s))
    | v => v
    end
  | If _ then_ else_ => Some ($0 $+ (wrap then_, s) $+ (wrap else_, s))
  | While e body => Some ($0 $+ (wrap Skip, s) $+ (wrap (Sequence body (While e body)), s))
  end.

(* CHALLENGE #3: Update all of the theorems and lemmas below to work in the new
 * world.  Only their proofs, not their statements, will need changes; and only
 * a few of them need updating at all.  We suggest optimistically powering
 * through with the existing proofs, getting Coq to tell you when changes are
 * needed.
 * One tactic hint: you will face many goals of the form [subsumeds s s'], for
 * more specific values of [s] and [s'].  When the structures of the two sides
 * match up well, repeated application of [subsumeds_add] and [subsumeds_empty]
 * finishes the proof, and [eauto] will even do all that for you.  Sometimes the
 * structures of the two sides don't match up well, but you can rewrite the goal
 * so that the match is obvious.  For instance, if you're starting at this goal:
 *   [subsumeds ($0 $+ (a, n)) ($0 $+ (a, n) $+ (b, m))]
 * It will be helpful to run:
 *   [replace ($0 $+ (a, n) $+ (b, m)) with ($0 $+ (b, m) $+ (a, n)) by maps_equal.]
 * Afterward, [eauto] can finish the subgoal! *)

Lemma command_equal : forall c1 c2 : cmd, sumbool (c1 = c2) (c1 <> c2).
Proof.
  repeat decide equality.
Qed.

Theorem absint_step_ok : forall a, absint_sound a
  -> forall (s : astate a) v, compatible s v
  -> forall c v' c', step (v, c) (v', c')
                     -> forall wrap, exists ss s', absint_step s c wrap = Some ss
                                                   /\ ss $? wrap c' = Some s'
                                                   /\ compatible s' v'.
Proof.
  induct 2; simplify.

  do 2 eexists; propositional.
  simplify; equality.
  eauto.

  eapply IHstep in H0; auto.
  invert H0.
  invert H2.
  propositional.
  rewrite H2.
  eauto.

  do 2 eexists; propositional.
  simplify; equality.
  assumption.

  do 2 eexists; propositional.
  cases (command_equal (wrap c') (wrap else_)).
  simplify; equality.
  simplify; equality.
  assumption.

  do 2 eexists; propositional.
  simplify; equality.
  assumption.

  do 2 eexists; propositional.
  simplify; equality.
  assumption.

  do 2 eexists; propositional.
  cases (command_equal (wrap Skip) (wrap (body;; while e loop body done))).
  simplify; equality.
  simplify; equality.
  assumption.
Qed.

Inductive abs_step a : astate a * cmd -> astate a * cmd -> Prop :=
| AbsStep : forall s c ss s' c',
  absint_step s c (fun x => x) = Some ss
  -> ss $? c' = Some s'
  -> abs_step (s, c) (s', c').

Hint Constructors abs_step.

Definition absint_trsys a (c : cmd) := {|
  Initial := {($0, c)};
  Step := abs_step (a := a)
|}.

Inductive Rabsint a : valuation * cmd -> astate a * cmd -> Prop :=
| RAbsint : forall v s c,
  compatible s v
  -> Rabsint (v, c) (s, c).

Hint Constructors abs_step Rabsint.

Theorem absint_simulates : forall a v c,
  absint_sound a
  -> simulates (Rabsint (a := a)) (trsys_of v c) (absint_trsys a c).
Proof.
  simplify.
  constructor; simplify.

  exists ($0, c); propositional.
  subst.
  constructor.
  unfold compatible.
  simplify.
  equality.

  invert H0.
  cases st1'.
  eapply absint_step_ok in H1; eauto.
  invert H1.
  invert H0.
  propositional.
  eauto.
Qed.

Definition merge_astates a : astates a -> astates a -> astates a :=
  merge (fun x y =>
           match x with
           | None => y
           | Some x' =>
             match y with
             | None => Some x'
             | Some y' => Some (merge_astate x' y')
             end
           end).

Inductive oneStepClosure a : astates a -> astates a -> Prop :=
| OscNil :
  oneStepClosure $0 $0
| OscCons : forall ss c s ss' ss'',
  oneStepClosure ss ss'
  -> match absint_step s c (fun x => x) with
     | None => ss'
     | Some ss'' => merge_astates ss'' ss'
     end = ss''
  -> oneStepClosure (ss $+ (c, s)) ss''.

Definition subsumeds a (ss1 ss2 : astates a) :=
  forall c s1, ss1 $? c = Some s1
               -> exists s2, ss2 $? c = Some s2
                             /\ subsumed s1 s2.

Theorem subsumeds_refl : forall a (ss : astates a),
  subsumeds ss ss.
Proof.
  unfold subsumeds; simplify; eauto.
Qed.

Hint Resolve subsumeds_refl.

Lemma subsumeds_add : forall a (ss1 ss2 : astates a) c s1 s2,
  subsumeds ss1 ss2
  -> subsumed s1 s2
  -> subsumeds (ss1 $+ (c, s1)) (ss2 $+ (c, s2)).
Proof.
  unfold subsumeds; simplify.
  cases (command_equal c c0); subst; simplify; eauto.
  invert H1; eauto.
Qed.

Hint Resolve subsumeds_add.

Lemma subsumeds_empty : forall a (ss : astates a),
  subsumeds $0 ss.
Proof.
  unfold subsumeds; simplify.
  equality.
Qed.

Lemma subsumeds_add_left : forall a (ss1 ss2 : astates a) c s,
  ss2 $? c = Some s
  -> subsumeds ss1 ss2
  -> subsumeds (ss1 $+ (c, s)) ss2.
Proof.
  unfold subsumeds; simplify.
  cases (command_equal c c0); subst; simplify; eauto.
  invert H1; eauto.
Qed.

Inductive interpret a : astates a -> astates a -> astates a -> Prop :=
| InterpretDone : forall ss1 any ss2,
  oneStepClosure ss1 ss2
  -> subsumeds ss2 ss1
  -> interpret ss1 any ss1
| InterpretStep : forall ss worklist ss' ss'',
  oneStepClosure worklist ss'
  -> interpret (merge_astates ss ss') ss' ss''
  -> interpret ss worklist ss''.

Lemma oneStepClosure_sound : forall a, absint_sound a
  -> forall ss ss' : astates a, oneStepClosure ss ss'
  -> forall c s s' c', ss $? c = Some s
                       -> abs_step (s, c) (s', c')
                          -> exists s'', ss' $? c' = Some s''
                                         /\ subsumed s' s''.
Proof.
  induct 2; simplify.

  equality.

  cases (command_equal c c0); subst; simplify.

  invert H2.
  invert H3.
  rewrite H5.
  unfold merge_astates; simplify.
  rewrite H7.
  cases (ss' $? c').
  eexists; propositional.
  unfold subsumed; simplify.
  unfold merge_astate; simplify.
  cases (s' $? x); try equality.
  cases (a0 $? x); simplify; try equality.
  invert H1; eauto.
  eauto.

  apply IHoneStepClosure in H3; auto.
  invert H3; propositional.
  cases (absint_step s c (fun x => x)); eauto.
  unfold merge_astates; simplify.
  rewrite H3.
  cases (a0 $? c'); eauto.
  eexists; propositional.
  unfold subsumed; simplify.
  unfold merge_astate; simplify.
  specialize (H4 x0).
  cases (s' $? x0).
  cases (a1 $? x0); try equality.
  cases (x $? x0); try equality.
  invert 1.
  eauto.

  rewrite H4.
  cases (a1 $? x0); equality.
Qed.

Lemma absint_step_monotone_None : forall a (s : astate a) c wrap,
    absint_step s c wrap = None
    -> forall s' : astate a, absint_step s' c wrap = None.
Proof.
  induct c; simplify; try equality.
  cases (absint_step s c1 (fun c => wrap (c;; c2))); equality.
Qed.

Lemma absint_interp_monotone : forall a, absint_sound a
  -> forall (s : astate a) e s' n,
    a.(Represents) n (absint_interp e s)
    -> subsumed s s'
    -> a.(Represents) n (absint_interp e s').
Proof.
  induct e; simplify; eauto.

  cases (s' $? x); eauto.
  cases (s $? x); eauto.
Qed.

Hint Resolve absint_interp_monotone.

Hint Resolve subsumeds_empty.

Lemma absint_step_monotone : forall a, absint_sound a
    -> forall (s : astate a) c wrap ss,
      absint_step s c wrap = Some ss
      -> forall s', subsumed s s'
                    -> exists ss', absint_step s' c wrap = Some ss'
                                   /\ subsumeds ss ss'.
Proof.
  induct c; simplify.

  equality.

  invert H0.
  eexists; propositional.
  eauto.
  apply subsumeds_add; eauto.

  cases (absint_step s c1 (fun c => wrap (c;; c2))).

  invert H0.
  eapply IHc1 in Heq; eauto.
  invert Heq; propositional.
  rewrite H2; eauto.

  invert H0.
  eapply absint_step_monotone_None in Heq; eauto.
  rewrite Heq; eauto.

  invert H0; eauto.

  invert H0; eauto.
Qed.

Lemma abs_step_monotone : forall a, absint_sound a
  -> forall (s : astate a) c s' c',
    abs_step (s, c) (s', c')
    -> forall s1, subsumed s s1
                  -> exists s1', abs_step (s1, c) (s1', c')
                                 /\ subsumed s' s1'.
Proof.
  invert 2; simplify.
  eapply absint_step_monotone in H4; eauto.
  invert H4; propositional.
  apply H3 in H6.
  invert H6; propositional; eauto.
Qed.

Lemma interpret_sound' : forall c a, absint_sound a
  -> forall ss worklist ss' : astates a, interpret ss worklist ss'
    -> ss $? c = Some $0
    -> invariantFor (absint_trsys a c) (fun p => exists s, ss' $? snd p = Some s
                                                           /\ subsumed (fst p) s).
Proof.
  induct 2; simplify; subst.

  apply invariant_induction; simplify; propositional; subst; simplify; eauto.

  invert H3; propositional.
  cases s.
  cases s'.
  simplify.
  eapply abs_step_monotone in H4; eauto.
  invert H4; propositional.
  eapply oneStepClosure_sound in H4; eauto.
  invert H4; propositional.
  eapply H1 in H4.
  invert H4; propositional.
  eauto using subsumed_trans.

  apply IHinterpret.
  unfold merge_astates; simplify.
  rewrite H2.
  cases (ss' $? c); trivial.
  unfold merge_astate; simplify; equality.
Qed.

Theorem interpret_sound : forall c a (ss : astates a),
  absint_sound a
  -> interpret ($0 $+ (c, $0)) ($0 $+ (c, $0)) ss
  -> invariantFor (absint_trsys a c) (fun p => exists s, ss $? snd p = Some s
                                                         /\ subsumed (fst p) s).
Proof.
  simplify.
  eapply interpret_sound'; eauto.
  simplify; equality.
Qed.

Ltac interpret_simpl := unfold merge_astates, merge_astate;
                       simplify; repeat simplify_map.
Ltac oneStepClosure := apply OscNil
                       || (eapply OscCons; [ oneStepClosure
                                           | interpret_simpl; reflexivity ]).
Ltac interpret1 := eapply InterpretStep; [ oneStepClosure | interpret_simpl ].
Ltac interpret_done := eapply InterpretDone; [ oneStepClosure
  | repeat (apply subsumeds_add_left || apply subsumeds_empty); (simplify; equality) ].


(** * Now, let's see a conditional-aware analysis in action! *)

(* CHALLENGE #4: Prove that this particular program only finishes in states
 * where ["b"] is even.  The old analysis wouldn't realize that one branch of
 * the final conditional is impossible. *)
Example loopomatic :=
  ("a" <- 1;;
   while "n" loop
     "a" <- "a" + 2 * "n";;
     "n" <- "n" - 1
   done;;
   when "a" then
     "b" <- 0
   else
     "b" <- 1
   done).

(* OK, so the main challenge here is waiting for Coq to finishing processing
 * proof scripts, since we've given you all the code. ;) *)

(* Now two lemmas that we prove to help the [simplify] tactic reduce uses of
 * [merge_astates]. *)

Lemma merge_astates_fok_parity : forall x : option (astate parity_absint),
  match x with Some x' => Some x' | None => None end = x.
Proof.
  simplify; cases x; equality.
Qed.

Lemma merge_astates_fok2_parity : forall x (y : option (astate parity_absint)),
    match y with
    | Some y' => Some (merge_astate x y')
    | None => Some x
    end = None -> False.
Proof.
  simplify; cases y; equality.
Qed.

Hint Resolve merge_astates_fok_parity merge_astates_fok2_parity.

(* Here's a utility theorem we used in lecture, too. *)
Lemma final_even : forall (s s' : astate parity_absint) v x,
  compatible s v
  -> subsumed s s'
  -> s' $? x = Some Even
  -> exists n, v $? x = Some n /\ isEven n.
Proof.
  unfold compatible, subsumed; simplify.
  specialize (H x); specialize (H0 x).
  cases (s $? x); simplify.

  rewrite Heq in *.
  assert (Some d = Some d) by equality.
  apply H in H2.
  first_order.

  eapply H0 in H1.
  invert H1.
  eauto.
  assumption.

  rewrite Heq in *.
  equality.
Qed.

Theorem loopomatic_even : forall v,
  invariantFor (trsys_of v loopomatic)
               (fun p => snd p = Skip
                         -> exists n, fst p $? "b" = Some n /\ isEven n).
Proof.
  simplify.
  eapply invariant_weaken.

  unfold loopomatic.
  eapply invariant_simulates.
  apply absint_simulates with (a := parity_absint).
  apply parity_sound.

  apply interpret_sound.
  apply parity_sound.

  (* The rest of this depends on your new interpreter being plugged in.
   * The exact number of iterations required below might vary, based on the
   * exact changes you make to the original framework. *)
(*
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret_done.

  invert 1.
  first_order.
  invert H0; simplify.
  invert H1.
  eapply final_even; eauto; simplify; try equality.
Qed.
*)
Admitted.
