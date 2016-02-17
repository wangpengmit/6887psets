(** * 6.887 Formal Reasoning About Programs - Lab 2
    * Transition Systems and Invariants, including modeling dynamic thread creation *)

Require Import Frap.

Set Implicit Arguments.

(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)

(* Examples based on ideas introduced in TransitionSystem.v, from the book source.
 * Key definitions about invariants are imported from the Frap library. *)


(** * A simple transition-system example: list search *)

(* Consider a transition system equivalent to this program, which checks whether
 * a number appears in a list:
   lsearch(needle, haystack) {
     while (haystack != null) {
       if (haystack.data == needle) {
         return true;
       } else {
         haystack = haystack.next;
       }
     }
     return false;
   } *)

(* Here's a suitable state type. *)
Inductive lsearch_state :=
| AnswerIs (answer : bool)
  (* The function has returned, with this answer. *)
| Searching (remaining : list nat).
  (* We are right before a loop iteration, with this value of "haystack". *)

(* Initial states: searching the full input list. *)
Inductive lsearch_init (haystack : list nat) : lsearch_state -> Prop :=
| LsearchInit : lsearch_init haystack (Searching haystack).

(* Steps, each corresponding to one loop iteration. *)
Inductive lsearch_step (needle : nat) : lsearch_state -> lsearch_state -> Prop :=
| LsearchNotFound :
  lsearch_step needle (Searching nil) (AnswerIs false)
| LsearchFound : forall ls,
  lsearch_step needle (Searching (needle :: ls)) (AnswerIs true)
| LsearchKeepLooking : forall x ls,
  x <> needle
  -> lsearch_step needle (Searching (x :: ls)) (Searching ls).

(* Putting it together into a full system, parameterized on the two function
 * parameters. *)
Definition lsearch_sys (needle : nat) (haystack : list nat) := {|
  Initial := lsearch_init haystack;
  Step := lsearch_step needle
|}.

(* A basic invariant capturing the final correctness condition. *)
Definition lsearch_correct (needle : nat) (haystack : list nat) (st : lsearch_state) :=
  match st with
  | AnswerIs b => b = true <-> In needle haystack
  | _ => True
  end.
(* Note the use of infix operator [<->] for "if and only if."
 * The [propositional] tactic knows what to do with it!
 * Also see the definition of [In], a predicate we use for list membership. *)
Print In.

(* CHALLENGE #1: Prove that the system meets its spec. *)
Theorem lsearch_ok : forall needle haystack,
  invariantFor (lsearch_sys needle haystack) (lsearch_correct needle haystack).
Proof.
Admitted.

(* Hint: You will almost certainly want to define and use a stronger
 * invariant! *)


(** * Transition systems for dynamic thread creation *)

(* Let's define a general way of building transition systems that allow dynamic
 * thread creation.  We will work with step relations returning values in this
 * type, capturing whether to spawn a new thread. *)
Inductive thread_step_outcome shared private :=
| Basic (sh : shared) (pr : private)
  (* Meaning: shared state is mutated to [sh] and private state to [pr]. *)
| Spawn (sh : shared) (state_of_new_thread my_own_next_state : private).
  (* Meaning: shared state to [sh] and private state to [my_own_next_state].
   * Additionally, spawn a new thread whose private state is
   * [state_of_new_thread]. *)

(* Now system states can include arbitrarily many threads. *)
Record threads_state shared private := {
  Shared : shared;
  (* State shared across all threads *)
  Private : list private
  (* Private states of all threads that have been spawned *)
}.

(* Initial states of multithreaded programs, based on given initial values of
 * shared and private state.  We start with exactly one thread, which has that
 * private state. *)
Inductive threads_init shared private (sh0 : shared) (pr0 : private)
  : threads_state shared private -> Prop :=
| ThreadsInit : threads_init sh0 pr0 {| Shared := sh0; Private := [pr0] |}.

(* CHALLENGE #2: Fill in this definition of a step relation.
 * To get more of a sense for the definitions, it may be helpful to look first
 * at the example system just below.
 * Another hint: you probably want to write rules that pick threads out of lists
 * and then build new modified lists.  A useful pattern for that picking is as
 * follows:
 *   [forall ts1 t ts2, threads_step step (... (ts1 ++ t :: ts2) ...)
 *                                        (... (ts1 ++ t' :: ts2) ...)]
 * That is, we quantify over all threads before and after a given thread [t],
 * in the list of active threads.  Recall that [++] is list concatenation,
 * while [::] is the operator to add a new element to the front of a list.
 *)
Inductive threads_step shared private
          (step : shared -> private -> thread_step_outcome shared private -> Prop)
  : threads_state shared private -> threads_state shared private -> Prop :=
| ThisIsWrong : forall sh pr sh' pr',
    threads_step step {| Shared := sh; Private := pr |}
                      {| Shared := sh'; Private := pr' |}.

(* Package it all together into a system. *)
Definition threads_sys shared private (sh0 : shared) (pr0 : private)
           (step : shared -> private -> thread_step_outcome shared private -> Prop)
  : trsys (threads_state shared private) := {|
  Initial := threads_init sh0 pr0;
  Step := threads_step step
|}.

(* Now our example of a thread-spawning program.  It is for checking whether a
 * number occurs in a binary tree, based on this type definition. *)
Inductive tree :=
| Leaf (n : nat)
| Branch (tr1 tr2 : tree).

(* Here is what it means for a number to be in the tree. *)
Fixpoint InTree (n : nat) (tr : tree) : Prop :=
  match tr with
  | Leaf n' => n = n'
  | Branch tr1 tr2 => InTree n tr1 \/ InTree n tr2
  end.

(* The pseudocode of our algorithm, where we write "spawn(c)" for running
 * command "c" in a new thread:

   bool found = false;

   treesearch(needle, haystack) {
     switch (haystack) {
       case Leaf n:
         if (n == needle) {
           found = true;
         }
         return;
       case Branch tr1 tr2:
         spawn(treesearch(needle, tr1));
         treesearch(needle, tr2);
     }
   }

 * If global variable "found" is ever set to "true", then we know the number
 * has been found in the tree.
*)

(* We only need to model the following two private program states. *)
Inductive treesearch_thread :=
| SearchTree (tr : tree)
  (* Just beginning a call to the function, searching the given tree *)
| Done.
  (* Finished a call to the function *)

(* Step relation, crucially using the [Spawn] outcome in the last rule *)
Inductive treesearch_step (needle : nat) : bool
  -> treesearch_thread
  -> thread_step_outcome bool treesearch_thread
  -> Prop :=
| TsLeafMatch : forall b,
  treesearch_step needle b (SearchTree (Leaf needle)) (Basic true Done)
| TsLeafNoMatch : forall b n,
  n <> needle
  -> treesearch_step needle b (SearchTree (Leaf n)) (Basic b Done)
| TsBranch : forall b tr1 tr2,
  treesearch_step needle b (SearchTree (Branch tr1 tr2))
                  (Spawn b (SearchTree tr1) (SearchTree tr2)).

Definition treesearch_sys (needle : nat) (haystack : tree) :=
  threads_sys false (SearchTree haystack) (treesearch_step needle).

(* Next, we use a helper function to define an overall correctness condition. *)
Fixpoint allDone (ls : list treesearch_thread) : Prop :=
  match ls with
  | nil => True
  | th :: ls' => th = Done /\ allDone ls'
  end.

Definition treesearch_correct (needle : nat) (haystack : tree)
           (st : threads_state bool treesearch_thread) :=
  allDone st.(Private)
  -> (InTree needle haystack <-> st.(Shared) = true).

(* CHALLENGE #3: Prove that the system meets its spec. *)
Theorem treesearch_ok : forall needle haystack,
  invariantFor (treesearch_sys needle haystack) (treesearch_correct needle haystack).
Proof.
Admitted.

(* Hint: you probably want to define another helper function or two, similar to
 * [allDone], to use in your strengthened invariant. *)

(* Some suggested tactics:
 * [left] or [right]: prove a disjunction (using [\/]) by choosing to prove the
 *   left or right disjunct, respectively.
 * [first_order]: simplify with rules of first-order logic.
 *   WARNING: Sometimes this one goes off the rails and runs effectively
 *   forever!
 * [rewrite H1 in H2]: use [H1] to make a rewrite as usual, but within
 *   hypothesis [H2], rather than in the conclusion formula.
 * [apply H1 in H2]: forward-reasoning version of [apply], for when [H1] proves
 *   an implication from [H2].  The effect is to replace [H2] with the
 *   conclusion of the implication.
 * [unfold X in *]: like [unfold X] but applies to the whole goal, not just the
 *   conclusion.
 * [exfalso]: switch to proving [False], from any conclusion.  That is, we
 *   switch into a proof by contradiction. *)
