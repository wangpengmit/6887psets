(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 3 *)

Require Import Frap Pset3Sig.

Set Implicit Arguments.


Theorem predicate_abstraction_simulates : forall pc state action
  (pc0 : pc) (st0 : state)
  (actionOf : pc -> action -> pc -> Prop)
  (doAction : action -> state -> state -> Prop)
  (pa : predicate_abstraction state action),
  predicate_abstraction_sound doAction pa
  -> simulates (paR pa)
               (actionSys pc0 st0 actionOf doAction)
               (predicate_abstract pc0 actionOf pa).
Proof.
Admitted.


(* Optional part: using predicate abstraction for another example *)

Import Program2 ZArith.


(* This is not the right abstraction. :-) *)
Definition sys_pa : predicate_abstraction state action := {|
  Predicates := $0;
  Rules := $0 $+ (LockOK, [])
              $+ (AssignA, [])
              $+ (IfFalse, [])
              $+ (IfTrue, [])
              $+ (UnlockOK, [])
              $+ (IncA, [])
              $+ (WhileFalse, [])
              $+ (WhileTrue, [])
|}.

Opaque Zplus. (* Important to keep Coq from trying too hard to help and
               * unfolding the definition of addition for integers! *)

Theorem sys_ok : forall np npo,
  invariantFor (sys np npo) (fun st => fst st = Unlock2 -> (snd st).(HasLock) = true).
Proof.
Admitted.
