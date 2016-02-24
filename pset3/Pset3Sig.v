(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 3 *)

Require Import Frap.

Set Implicit Arguments.


(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)

(* In our classroom discussion of abstraction for model checking, there, were
 * some objections that writing and proving an abstraction feels like just as
 * much work as finding an invariant in the first place.  In this pset, we'll
 * examine a kind of abstraction where the payoff is clearer, because the author
 * of the abstraction only needs to think about the effects of the different
 * atomic statements in the program, not the control flow that connects them to
 * each other.  Many different abstraction techniques work well in that setting,
 * and we will develop just one of them, *predicate abstraction*, which has been
 * used quite successfully in fully automated tools like SLAM and BLAST.  In
 * this pset, we'll write predicate abstractions manually, but the overall idea
 * can be proved sound once and for all. *)

(* First, here's a generic step relation parameterized over a few types and
 * relations. *)
Inductive step
          pc     (* This is the type of program-counter locations. *)
          state  (* This is the type of variable values. *)
          action (* Variables are changed by actions from this set. *)

          (actionOf : pc -> action -> pc -> Prop)
          (* This relation explains which actions can run from which program
           * counters, taking us to particular new program counters.  It's very
           * similar to the step relation of a deterministic finite automaton
           * (DFA), where "actions" would be characters of a finite alphabet. *)

          (doAction : action -> state -> state -> Prop)
          (* This relation explains which effects each action might have on
           * states. *)

  : pc * state -> pc * state -> Prop :=
| StepAction : forall pc1 act pc2 st1 st2,
  actionOf pc1 act pc2
  -> doAction act st1 st2
  -> step actionOf doAction (pc1, st1) (pc2, st2).
(* Notice the clean split between [doAction], for modeling the effects of
 * actions, and [actionOf], for explaining which actions a particular program
 * could trigger.  We will develop an abstraction technique that lets us focus
 * on [doAction] alone. *)

(* Here's a wrapper to create a proper transition system, given the relations
 * initial values for the program counter and state. *)
Definition actionSys pc state action (pc0 : pc) (st0 : state)
           (actionOf : pc -> action -> pc -> Prop)
           (doAction : action -> state -> state -> Prop)
           : trsys (pc * state) := {|
  Initial := {(pc0, st0)};
  Step := step actionOf doAction
|}.

(* Now, we begin defining predicate abstraction.  In general, this abstraction
 * will involve tracking the values of some finite set of logical *predicates*
 * over the state (program variables).  We will represent predicates with
 * strings, written here with the type synonym [var]. *)

(* This type captures a single assertion: a predicate is known to be either
 * true or false. *)
Record assertion := {
  AssumedPredicate : var;
  AssumedToBe : bool
}.

(* A *rule* gives us a way to deduce the *new* value of a predicate, given the
 * *old* values of other predicates, before some action. *)
Record rule := {
  Assumptions : list assertion;
  Conclusion : assertion
}.

(* A predicate abstraction gives us two key ingredients. *)
Record predicate_abstraction state action := {
  Predicates : fmap var (state -> Prop);
  (* We include these predicates, explaining the meaning of each by mapping it
   * to the logical notion of a predicate on states. *)

  Rules : fmap action (list rule)
  (* These rules show, for each action, how we may update the truth values of
   * the predicates we are tracking. *)
}.

(* This predicate formalizes the meaning of an assertion, given a map assigning
 * known truth values to (some of) the predicates. *)
Definition assertionHolds (st : fmap var bool) (asr : assertion) : bool :=
  match asr with
  | {| AssumedPredicate := p; AssumedToBe := b |} =>
    match st $? p with
    | None => false
    | Some true => b
    | Some false => negb b
    end
  end.

(* We can lift the operation to check that every assumption in a list holds,
 * instead of just one of them. *)
Fixpoint assumptionsHold (st : fmap var bool) (asms : list assertion) : bool :=
  match asms with
  | nil => true
  | asm :: asms' => assertionHolds st asm && assumptionsHold st asms'
  end.

(* Given a predicate state [st] from before running an action, where rule [r]
 * explains the effects of that action, *extend* predicate state [st'] with the
 * additional predicates that [r] allows us to deduce. *)
Definition applyRule (st st' : fmap var bool) (r : rule)
  : fmap var bool :=
  match r with
  | {| Assumptions := asns; Conclusion := conc |} =>
    if assumptionsHold st asns
    then st' $+ (conc.(AssumedPredicate), conc.(AssumedToBe))
    else st'
  end.

(* Iterate the above logic for multiple rules. *)
Fixpoint applyRules (st st' : fmap var bool) (rs : list rule)
  : fmap var bool :=
  match rs with
  | nil => st'
  | r :: rs' => applyRules st (applyRule st st' r) rs'
  end.

(* We use that operation to implement a step relation. *)
Inductive predicate_step pc action (actionOf : pc -> action -> pc -> Prop)
          (rules : fmap action (list rule))
  : pc * fmap var bool -> pc * fmap var bool -> Prop :=
| PredicateStep : forall pc1 act pc2 pm,
  actionOf pc1 act pc2
  -> predicate_step actionOf rules (pc1, pm) (pc2, match rules $? act with
                                                   | None => $0
                                                   | Some rs => applyRules pm $0 rs
                                                   end).
(* Note a crucial effect of the [match]: when an action is not in the rules map,
 * we conservatively pick the state with no asserted predicates. *)

(* Finally, we bring it all together into a transition system. *)
Definition predicate_abstract pc state action (pc0 : pc)
           (actionOf : pc -> action -> pc -> Prop)
           (pa : predicate_abstraction state action) : trsys (pc * fmap var bool) := {|
  Initial := {(pc0, $0)};
  Step := predicate_step actionOf pa.(Rules)
|}.

(* Next, let's characterize what makes a particular rule set sound. *)

(* First, when is an assertion accurate, with respect to a concrete state
 * [st]? *)
Definition assertionAccurate state (predicates : fmap var (state -> Prop))
           (asr : assertion) (st : state) :=
  match predicates $? asr.(AssumedPredicate) with
  | None => False
  | Some pr => pr st <-> asr.(AssumedToBe) = true
  end.

(* Next, lift to lists of assertions. *)
Fixpoint assumptionsAccurate state (predicates : fmap var (state -> Prop))
         (asms : list assertion) (st : state) :=
  match asms with
  | nil => True
  | asm :: asms' => assertionAccurate predicates asm st
                    /\ assumptionsAccurate predicates asms' st
  end.

(* A rule is accurate when accuracy of its assumptions implies accuracy of its
 * conclusion, with respect to a particular relation [doIt] for performing some
 * action. *)
Definition ruleAccurate state (predicates : fmap var (state -> Prop))
           (doIt : state -> state -> Prop) (r : rule) :=
  forall st st', assumptionsAccurate predicates r.(Assumptions) st
                 -> doIt st st'
                 -> assertionAccurate predicates r.(Conclusion) st'.

(* A predicate abstraction is sound when every one of its rules, for every
 * action, is accurate. *)
Definition predicate_abstraction_sound state action
           (doAction : action -> state -> state -> Prop)
           (pa : predicate_abstraction state action) :=
  forall act rs r, pa.(Rules) $? act = Some rs
                   -> In r rs
                   -> ruleAccurate pa.(Predicates) (doAction act) r.

(* Here is a good simulation relation, to connect the original system to its
 * predicate abstraction. *)
Inductive paR pc state action (pa : predicate_abstraction state action)
  : pc * state -> pc * fmap var bool -> Prop :=
| PaR : forall pc0 st pm,
  (forall x b, pm $? x = Some b
               -> match pa.(Predicates) $? x with
                  | None => False
                  | Some pr => pr st <-> b = true
                  end)
  -> paR pa (pc0, st) (pc0, pm).

(* Here's the one theorem you're asking you to prove, for full credit. *)
Module Type S.
  (* Predicate abstraction really is a sound abstraction! *)
  Axiom predicate_abstraction_simulates : forall pc state action
    (pc0 : pc) (st0 : state)
    (actionOf : pc -> action -> pc -> Prop)
    (doAction : action -> state -> state -> Prop)
    (pa : predicate_abstraction state action),
    predicate_abstraction_sound doAction pa
    -> simulates (paR pa)
                 (actionSys pc0 st0 actionOf doAction)
                 (predicate_abstract pc0 actionOf pa).
End S.



(* Here's an example that might be useful to understand predicate
 * abstraction. *)

(*
  f(int n) {
    int a = 1;

    while (n > 0) {
      a = a + n;
      n = n - 1;
    }
  }
*)

Module Program1.

  Inductive pc := Initialize | Loop | IncrementA | DecrementN | Done.

  Require Import ZArith.
  Open Scope Z_scope.

  Record state := {
                   N : Z;
                   A : Z
                 }.

  Inductive action := AssignA | TestTrue | TestFalse | AddToA | SubtractFromN.

  Inductive actionOf : pc -> action -> pc -> Prop :=
  | ActInitialize : actionOf Initialize AssignA Loop
  | ActLoopTrue : actionOf Loop TestTrue IncrementA
  | ActLoopFalse : actionOf Loop TestFalse Done
  | ActIncrementA : actionOf IncrementA AddToA DecrementN
  | ActDecrementN : actionOf DecrementN SubtractFromN Loop.

  Inductive doAction : action -> state -> state -> Prop :=
  | DoAssignA : forall n a, doAction AssignA {| N := n; A := a |} {| N := n; A := 1 |}
  | DoTestTrue : forall n a, n > 0 -> doAction TestTrue {| N := n; A := a |} {| N := n; A := a |}
  | DoTestFalse : forall n a, n <= 0 -> doAction TestFalse {| N := n; A := a |} {| N := n; A := a |}
  | DoAddToA : forall n a, doAction AddToA {| N := n; A := a |} {| N := n; A := a + n |}
  | DoSubtractFromN : forall n a, doAction SubtractFromN {| N := n; A := a |} {| N := n-1; A := a |}.

  Definition sys n a := actionSys Initialize {| N := n; A := a |} actionOf doAction.

  (* Here's the rule set. *)
  Definition sys_pa := {|
    Predicates := $0 $+ ("a > 0", fun st => st.(A) > 0)
                     $+ ("n > 0", fun st => st.(N) > 0);
    Rules := $0 $+ (AssignA, [{|Assumptions := [];
                                Conclusion := {|AssumedPredicate := "a > 0";
                                                AssumedToBe := true|} |}])
              $+ (TestTrue, [{|Assumptions := [];
                               Conclusion := {|AssumedPredicate := "n > 0";
                                               AssumedToBe := true|} |};
                               {|Assumptions := [{|AssumedPredicate := "a > 0";
                                                   AssumedToBe := true|}];
                                 Conclusion := {|AssumedPredicate := "a > 0";
                                                 AssumedToBe := true|} |}])
              $+ (TestFalse, [{|Assumptions := [{|AssumedPredicate := "a > 0";
                                                  AssumedToBe := true|}];
                                Conclusion := {|AssumedPredicate := "a > 0";
                                                AssumedToBe := true|} |}])
              $+ (AddToA, [{|Assumptions := [{|AssumedPredicate := "a > 0";
                                               AssumedToBe := true|};
                                               {|AssumedPredicate := "n > 0";
                                                 AssumedToBe := true|}];
                             Conclusion := {|AssumedPredicate := "a > 0";
                                             AssumedToBe := true|} |}])
              $+ (SubtractFromN,  [{|Assumptions := [{|AssumedPredicate := "a > 0";
                                                       AssumedToBe := true|}];
                                     Conclusion := {|AssumedPredicate := "a > 0";
                                                     AssumedToBe := true|} |}])
  |}.

  Theorem sys_ok :
    (forall pc state action
        (pc0 : pc) (st0 : state)
        (actionOf : pc -> action -> pc -> Prop)
        (doAction : action -> state -> state -> Prop)
        (pa : predicate_abstraction state action),
        predicate_abstraction_sound doAction pa
        -> simulates (paR pa)
                     (actionSys pc0 st0 actionOf doAction)
                     (predicate_abstract pc0 actionOf pa))
    (* We assume the theorem we ask you above to prove. *)
    -> forall n a,
      invariantFor (sys n a) (fun st => fst st <> Initialize -> (snd st).(A) > 0).
  Proof.
    intro predicate_abstraction_simulates.
    simplify.
    eapply invariant_weaken.
    eapply invariant_simulates.
    eapply predicate_abstraction_simulates with (pa := sys_pa).

    unfold predicate_abstraction_sound; simplify.
    cases act; simplify; invert H; unfold ruleAccurate, assertionAccurate in *; simplify; propositional; subst;
      simplify.
    invert H1; simplify; propositional.
    linear_arithmetic.
    invert H1; simplify; propositional.
    unfold assertionAccurate in *; simplify.
    invert H1; simplify.
    propositional.
    unfold assertionAccurate in *; simplify.
    invert H1; simplify.
    propositional.
    unfold assertionAccurate in *; simplify.
    invert H1; simplify.
    propositional.
    linear_arithmetic.
    unfold assertionAccurate in *; simplify.
    invert H1; simplify.
    propositional.

    model_check_infer.

    simplify.
    invert H.
    simplify.
    propositional; subst.

    invert H1; simplify.
    propositional.

    invert H1; simplify.
    specialize (H3 "a > 0"); simplify.
    eapply H3; equality.
    (* Note a useful tactic here.
     * [specialize (H e)] instantiates [H]'s first quantifier with [e]. *)

    invert H1; simplify.
    specialize (H3 "a > 0"); simplify.
    eapply H3; equality.

    invert H1; simplify.
    specialize (H3 "a > 0"); simplify.
    eapply H3; equality.

    invert H1; simplify.
    specialize (H3 "a > 0"); simplify.
    eapply H3; equality.
  Qed.

End Program1.


(* Another example, not required to get full credit, but which you might find
 * worthwhile to finish, using predication abstraction *)

(* Here is a (simplified) snippet from a device driver for Microsoft Windows,
 * adapted from http://fm.csl.sri.com/SSFT12/predabs-SSFT12.pdf.

  <<
  do {
    lock();
    nPacketsOld = nPackets;
    if (request) {
       unlock();
       ++nPackets;
    }
  } while (nPackets == nPacketsOld);
  unlock();
  >>

  We want to prove that the locking principle, i.e. balance of lock/unlock, is obeyed. 
*)

Module Program2.
  Inductive pc := Lock | Assign | If | Unlock1 | Inc | While | Unlock2 | Done.

  Require Import ZArith.
  Open Scope Z_scope.

  Record state := {
                   NP : Z; (* nPackets*)
                   NPO : Z; (* nPacketsOld *)
                   HasLock : bool
                 }.

  Inductive action := LockOK | AssignA | IfFalse | IfTrue | UnlockOK | IncA | WhileFalse | WhileTrue.

  Inductive actionOf : pc -> action -> pc -> Prop :=
  | ActLock : actionOf Lock LockOK Assign
  | ActAssign : actionOf Assign AssignA If
  | ActIfFalse : actionOf If IfFalse While
  | ActIfTrue : actionOf If IfTrue Unlock1
  | ActUnlock1 : actionOf Unlock1 UnlockOK Inc
  | ActInc : actionOf Inc IncA While
  | ActWhileFalse : actionOf While WhileFalse Unlock2
  | ActWhileTrue : actionOf While WhileTrue Lock
  | ActUnlock2 : actionOf Unlock2 UnlockOK Done.

  Inductive doAction : action -> state -> state -> Prop :=
  | DoLock np npo l :
      doAction LockOK 
               {| NP := np; NPO := npo; HasLock := l |} 
               {| NP := np; NPO := npo; HasLock := true |}
  | DoAssignA np npo l :
      doAction AssignA
               {| NP := np; NPO := npo; HasLock := l |} 
               {| NP := np; NPO := np; HasLock := l |}
  | DoIfFalse np npo l :
      doAction IfFalse
               {| NP := np; NPO := npo; HasLock := l |} 
               {| NP := np; NPO := npo; HasLock := l |}
  | DoIfTrue np npo l :
      doAction IfTrue
               {| NP := np; NPO := npo; HasLock := l |} 
               {| NP := np; NPO := npo; HasLock := l |}
  | DoUnlock np npo l :
      doAction UnlockOK 
               {| NP := np; NPO := npo; HasLock := l |} 
               {| NP := np; NPO := npo; HasLock := false |}
  | DoIncA np npo l :
      doAction IncA
               {| NP := np; NPO := npo; HasLock := l |} 
               {| NP := 1 + np; NPO := npo; HasLock := l |}
  | DoWhileFalse np npo l :
      np <> npo ->
      doAction WhileFalse
               {| NP := np; NPO := npo; HasLock := l |} 
               {| NP := np; NPO := npo; HasLock := l |}
  | DoWhileTrue npo l :
      doAction WhileTrue
               {| NP := npo; NPO := npo; HasLock := l |} 
               {| NP := npo; NPO := npo; HasLock := l |}.

  Definition sys np npo :=
    actionSys Lock {| NP := np; NPO := npo; HasLock := false |} actionOf doAction.

  (* Here's the theorem to prove.
   * Warning: even on my workstation, with a good predicate abstraction, it
   * takes on the order of 10 minutes to model check!  *)
  Theorem sys_ok : forall np npo,
    invariantFor (sys np npo) (fun st => fst st = Done -> (snd st).(HasLock) = false).
  Proof.
  Admitted.

End Program2.
