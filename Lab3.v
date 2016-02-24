(** * 6.887 Formal Reasoning About Programs - Lab 3
    * Model Checking, including abstraction *)

Require Import Frap.

Set Implicit Arguments.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)

(* Examples based on ideas introduced in ModelChecking.v, from the book source.
 * Key definitions about model checking are imported from the Frap library. *)

(* Use model checking to verify the following program
 * against the property that j==3 when the program finishes.

  <<
  int i = 0;
  int j = 0;

  void foo() {
    while (i <= 2){
      ++i;
      ++j;
    }
  }
  >>
*)

(* CHALLENGE #1: We've made a small mistake in formalizing this program as a
 * transition system.  Correct the mistake.  (Otherwise, the program will not,
 * in fact, satisfy the spec!) *)

Inductive pc :=
| Loop
| i_add_1
| j_add_1
| Done.

Record vars := {
  I : nat;
  J : nat
}.

Record state := {
  Pc : pc;
  Vars : vars
}.

Definition foo_init := { {| Pc := Loop; Vars := {| I := 0; J := 0 |} |} }.

Inductive step : state -> state -> Prop :=
| Step_Loop_done : forall i j,
    step {| Pc := Loop; Vars := {| I := i;
                                   J := j |} |}
         {| Pc := Done; Vars := {| I := i;
                                   J := j |} |}
| Step_Loop_enter : forall i j,
    step {| Pc := Loop; Vars := {| I := i;
                                   J := j |} |}
         {| Pc := i_add_1; Vars := {| I := i;
                                      J := j |} |}
| Step_i_add_1 : forall i j,
    step {| Pc := i_add_1; Vars := {| I := i;
                                      J := j |} |}
         {| Pc := j_add_1; Vars := {| I := 1 + i;
                                      J := j |} |}
| Step_j_add_1 : forall i j,
    step {| Pc := j_add_1; Vars := {| I := i;
                                      J := j |} |}
         {| Pc := Loop; Vars := {| I := i;
                                   J := 1 + j |} |}.

Definition foo_sys := {|
  Initial := foo_init;
  Step := step
|}.

Definition foo_correct (st : state) :=
  st.(Pc) = Done -> st.(Vars).(J) = 3.

(* A hint to help the model checker, related to when to unfold definitions *)
Arguments foo_correct / .

(* CHALLENGE #2: Prove the system correct.
 * WARNING: with the broken system above, the model checker is likely to run for
 * intractably long!  However, when you fix the system definition, this should
 * be a very easy proof, thanks to the magic of automatic state-space
 * exploration. *)
Theorem foo_ok :
  invariantFor foo_sys foo_correct.
Proof.
Admitted.


(* Next, we'll look at verifying the following two-thread producer/consumer
 * program against the property that MIN <= x <= MAX always holds.

  <<
  x = MIN;

  void producer(){
    while(true){
      lock();
      if (x < MAX) {
        ++x;
      }
      unlock();
    }
  } 

  void consumer(){
    while(true){
      lock();
      if (x > MIN) {
        --x;
      }
      unlock();
    }
  } 
  >>
*)

(* Here's our formal encoding of the system, which this time you can trust to be
 * correct. *)

Notation num := nat.

Section prco.
  (* We use sections and variables to introduce local, unknown parameters. *)
  Variable MIN : num.
  Variable MAX : num.
  
  Record shared_state val := { Locked : bool; X : val }.

  Inductive producer_pc :=
  | PrLock
  | PrTest
  | PrInc
  | PrUnlock.

  Definition producer_state := threaded_state (shared_state num) producer_pc.

  Definition producer_init := { {| Shared := {| Locked := false; X := MIN |};
                                   Private := PrLock |} }.

  Inductive producer_step : producer_state -> producer_state -> Prop :=
  | PrStep_Lock : forall x,
      producer_step {| Shared := {| Locked := false; X := x|}; Private := PrLock |}
                    {| Shared := {| Locked := true; X := x|}; Private := PrTest |}
  | PrStep_Test_true : forall l x,
      x < MAX ->
      producer_step {| Shared := {| Locked := l; X := x|}; Private := PrTest |}
                    {| Shared := {| Locked := l; X := x|}; Private := PrInc |}
  | PrStep_Test_false : forall l x,
      x >= MAX ->
      producer_step {| Shared := {| Locked := l; X := x|}; Private := PrTest |}
                    {| Shared := {| Locked := l; X := x|}; Private := PrUnlock |}
  | PrStep_Inc : forall l x,
      producer_step {| Shared := {| Locked := l; X := x|}; Private := PrInc |}
                    {| Shared := {| Locked := l; X := 1 + x|}; Private := PrUnlock |}
  | PrStep_Unlock : forall l x,
      producer_step {| Shared := {| Locked := l; X := x|}; Private := PrUnlock |}
                    {| Shared := {| Locked := false; X := x|}; Private := PrLock |}.

  Definition producer_sys := {|
    Initial := producer_init;
    Step := producer_step
  |}.

  Inductive consumer_pc :=
  | CoLock
  | CoTest
  | CoDec
  | CoUnlock.

  Definition consumer_state := threaded_state (shared_state num) consumer_pc.

  Definition consumer_init := { {| Shared := {| Locked := false; X := MIN |};
                                   Private := CoLock |} }.

  Inductive consumer_step : consumer_state -> consumer_state -> Prop :=
  | CoStep_Lock : forall x,
      consumer_step {| Shared := {| Locked := false; X := x|}; Private := CoLock |}
                    {| Shared := {| Locked := true; X := x|}; Private := CoTest |}
  | CoStep_Test_true : forall l x,
      x > MIN ->
      consumer_step {| Shared := {| Locked := l; X := x|}; Private := CoTest |}
                    {| Shared := {| Locked := l; X := x|}; Private := CoDec |}
  | CoStep_Test_false : forall l x,
      x <= MIN ->
      consumer_step {| Shared := {| Locked := l; X := x|}; Private := CoTest |}
                    {| Shared := {| Locked := l; X := x|}; Private := CoUnlock |}
  | CoStep_Dec : forall l x,
      consumer_step {| Shared := {| Locked := l; X := x|}; Private := CoDec |}
                    {| Shared := {| Locked := l; X := x - 1|}; Private := CoUnlock |}
  | CoStep_Unlock : forall l x,
      consumer_step {| Shared := {| Locked := l; X := x|}; Private := CoUnlock |}
                    {| Shared := {| Locked := false; X := x|}; Private := CoLock |}.

  Definition consumer_sys := {|
    Initial := consumer_init;
    Step := consumer_step
  |}.

  Definition prco_sys := parallel producer_sys consumer_sys.

  Definition prco_state := threaded_state (shared_state num) (producer_pc * consumer_pc).

  Definition prco_correct (s : prco_state) :=
    MIN <= s.(Shared).(X) <= MAX.

  (* Let's re-express the combined initial state as a singleton set. *)
  Theorem prco_init_is :
    parallel1 producer_init consumer_init = { {| Shared := {| Locked := false; X := MIN|};
                                                 Private := (PrLock, CoLock) |} }.
  Proof.
    simplify.
    apply sets_equal; simplify.
    propositional.
    {
      invert H; invert H2; invert H4; equality.
    }
    invert H0.
    repeat constructor.
  Qed.

End prco.

Hint Rewrite prco_init_is.
Arguments prco_correct / .

(* We can try model checking [proco_sys] with different [MIN] and [MAX]
 * values. *)
Theorem prco_ok_example :
  invariantFor (prco_sys 1 2) (prco_correct 1 2).
Proof.
  Time model_check_find_invariant.
  model_check_finish.
Qed.

(* But the time for model checking grows rapidly with larger constants.
 * We should apply abstraction. *)

(* CHALLENGE #3: Come up with a suitable abstraction of this system and use it
 * to verify the original program *for all [MIN] and [MAX] values (assuming 0 < MIN < MAX)*, by reduction
 * to a finite-state system that can be model checked. *)

Section prco_a.

  Variable MIN : num.
  Variable MAX : num.
  (* We make this assumption about MIN and MAX, which becomes a hypothesis that can be used in the following part of the section *)
  Hypothesis MIN_MAX : 0 < MIN < MAX.
  
  Theorem prco_ok :
    invariantFor (prco_sys MIN MAX) (prco_correct MIN MAX).
  Proof.
  Admitted.

End prco_a.
