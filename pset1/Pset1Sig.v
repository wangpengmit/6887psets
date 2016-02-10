(** * 6.887 Formal Reasoning About Programs - Lab 1 *)

Require Import Frap.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)

(** * MapReduce *)

(* *MapReduce* is a popular model for distributed computing in data centers.  See:
 *   https://en.wikipedia.org/wiki/MapReduce
 * But we'll explain our tiny subset of it from scratch here and prove some
 * algebraic properties.  We'll make the simplifying assumption that every
 * MapReduce job starts as a list of natural numbers.  Our goal is to compute
 * some summary of such lists. *)

(* The first step of a MapReduce job is a *map*, which applies a pure function
 * to every element of the input list, producing a new derived list.
 * We can define a syntactic type of allowed map operations. *)
Inductive map_ :=
| Constant (n : nat)
| Input 
| Add (e1 e2 : map_)
| Compose (e1 e2 : map_).

(* After replacing each input element with some new value, we apply some
 * operator repeatedly to reduce to a final summary.  Here are the operators
 * supported in our modest simplification. *)
Inductive reduce :=
| Sum
| Max.

(* Paired together, they form a whole MapReduce task. *)
Definition mapReduce := (map_ * reduce)%type.
                           (* ^-- pair type *)

(* Here's what a [map_] does to a number. *)
Fixpoint interp_map (e : map_) (x : nat) : nat :=
  match e with
  | Constant n => n
  | Input => x
  | Add e1 e2 => interp_map e1 x + interp_map e2 x
  | Compose e1 e2 => interp_map e1 (interp_map e2 x)
  end.

(* And here's what a [reduce] does to a list of numbers. *)
Definition interp_reduce (e : reduce) (ls : list nat) : nat :=
  match e with
  | Sum => fold_left plus ls 0
  | Max => fold_left max ls 0
  end.
(* It may be helpful to examine the definition of [fold_left]. *)
Print fold_left.

(* Now we have the overall MapReduce job executor. *)
Definition interp_mr (e : mapReduce) ls :=
  interp_reduce (snd e) (map (interp_map (fst e)) ls).
              (* ^-- projection functions --^ *)

(* Here's a simple condition on a [map_], capturing when it only contains
 * positive constants.  That will imply that, given a positive input, the
 * output is also positive, which you will prove, as specified below. *)
Fixpoint allPositive (m : map_) : Prop :=
  match m with
  | Constant n => n > 0
  | Input => True
  | Add m1 m2 => allPositive m1 /\ allPositive m2
  | Compose m1 m2 => allPositive m1 /\ allPositive m2
  end.

(* Finally, the module type listing the theorems that we ask you to prove. *)
Module Type S.
  (* Prove that [allPositive] means what we want it to mean. *)
  Axiom allPositive_ok : forall (m : map_) (x : nat),
    allPositive m
    -> x > 0
    -> interp_map m x > 0.

  (* Input order is irrelevant to the results of MapReduce jobs. *)
  Axiom reduce_swap : forall (e : reduce) (ls1 ls2 : list nat),
    interp_reduce e (ls1 ++ ls2) = interp_reduce e (ls2 ++ ls1).
  Axiom interp_swap : forall (e : mapReduce) (ls1 ls2 : list nat),
    interp_mr e (ls1 ++ ls2) = interp_mr e (ls2 ++ ls1).
  (* Note that a list of length [n] can, in general, be expressed as [n+1]
   * different concatenations of other lists.  These theorems tell us that
   * swapping at any split point in the input list preserves output values.
   * Iterating these results shows that any permutation on an input list leads
   * to the same output. *)

  (* Furthermore, we can decompose computation into arbitrary treelike structures.
   * That is, we can break the input list into chunks, or *partitions*, and
   * reduce them separately, then do a further reduce on those results.
   * Imagine a different server in a cluster assigned to each partition, so that
   * they can all run in parallel, saving significant time over treating the
   * whole input list sequentially. *)
  Axiom mapReduce_partition_two : forall (m : map_) (r : reduce) (ls1 ls2 : list nat),
    interp_mr (m, r) (ls1 ++ ls2) = interp_reduce r [interp_mr (m, r) ls1; interp_mr (m, r) ls2].
  Arguments app {_} _ _ . (* Some magic to allow us to use [app] below,
                           * without specifying its type parameter *)
  Axiom mapReduce_partition : forall (m : map_) (r : reduce) (lsls : list (list nat)),
    interp_mr (m, r) (fold_left app lsls []) = interp_reduce r (map (interp_mr (m, r)) lsls).
  (* Note that here [lsls], a list of lists, expresses an arbitrary division of
   * a list into contiguous partitions. *)
  
End S.


(* That's the end of the required part of this assignment.
 * Since we are still working on gauging difficulty, we're also including
 * another, optional part, in case you are looking for something else to do!
 * When you submit your solution, we'll appreciate your feedback on whether we
 * should have made this next part required. *)

(** * Interpreting unbounded loops *)

(* First, let's copy in the last lecture's interpreter for a loopy language. *)

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Definition valuation := fmap var nat.

Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0 (* goofy default value! *)
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| Repeat (e : arith) (body : cmd).

Fixpoint selfCompose {A} (f : A -> A) (n : nat) : A -> A :=
  match n with
  | O => fun x => x
  | S n' => fun x => selfCompose f n' (f x)
  end.

Fixpoint exec (c : cmd) (v : valuation) : valuation :=
  match c with
  | Skip => v
  | Assign x e => v $+ (x, interp e v)
  | Sequence c1 c2 => exec c2 (exec c1 v)
  | Repeat e body => selfCompose (exec body) (interp e v) v
  end.

(* That's the end of the copied code.  Next, we define a popular optimization
 * for languages of this type: *constant propagation*, which infers that certain
 * variables hold known values at certain points, so that mentions of those
 * variables can be *replaced* with constants. *)

(* This function applies constant propagation to an arithmetic expression.
 * It takes a variable valuation as an argument.  Recall that valuations are
 * *partial* finite maps; not all variables will be present.  In fact, even
 * fewer variables will be present than for the interpreter: we only include
 * mappings for those variables *whose values are known at compile time*.
 * Those are exactly the variables that we should replace in the expression! *)
Fixpoint constPropArith (e : arith) (v : valuation) : arith :=
  match e with
  | Const _ => e
  | Var x => match v $? x with
             | None => e
             | Some n => Const n (* Found a replaceable variable! *)
             end
  | Plus e1 e2 =>
    let e1' := constPropArith e1 v in
    let e2' := constPropArith e2 v in
    match e1', e2' with
    | Const n1, Const n2 => Const (n1 + n2)
    | _, _ => Plus e1' e2'
    end
  | Minus e1 e2 =>
    let e1' := constPropArith e1 v in
    let e2' := constPropArith e2 v in
    match e1', e2' with
    | Const n1, Const n2 => Const (n1 - n2)
    | _, _ => Minus e1' e2'
    end
  | Times e1 e2 =>
    let e1' := constPropArith e1 v in
    let e2' := constPropArith e2 v in
    match e1', e2' with
    | Const n1, Const n2 => Const (n1 * n2)
    | _, _ => Times e1' e2'
    end
  end.

(* Crucial helper function.  It takes in a valuation assigning constant values
 * to those variables where we can figure out the constants.  It then models how
 * that knowledge *changes* based on the effect of a command. *)
Fixpoint effectOf (c : cmd) (v : valuation) : valuation :=
  match c with
  | Skip => v
  | Assign x e =>
    let e' := constPropArith e v in
    match e' with
    | Const n =>
      v $+ (x, n)
      (* We inferred the value that is being assigned.
       * Record that knowledge in the valuation. *)
    | _ =>
      v $- x
      (* We couldn't be sure what value is assigned.
       * Conservatively, *remove* this variable from the valuation.
       * (Note the use of a new infix operator for removal.) *)
    end
  | Sequence c1 c2 =>
    effectOf c2 (effectOf c1 v)
    (* Crucial pattern: we take the effect of [c1], followed by the effect of
     * [c2]. *)
  | Repeat _ _ => $0
    (* It would take much more advanced analysis to summarize the effect of a
     * loop, so let's punt and return an empty set of knowledge. *)
  end.

(* OK, we come to the main transformation, parameterized on knowledge, like the
 * other functions have been. *)
Fixpoint constProp (c : cmd) (v : valuation) : cmd :=
  match c with
  | Skip => c
  | Assign x e => Assign x (constPropArith e v)
  | Sequence c1 c2 =>
    Sequence (constProp c1 v) (constProp c2 (effectOf c1 v))
    (* Here we have a crucial use of [effectOf], to expand the knowledge as we
     * descend into the second command. *)
  | Repeat e c1 =>
    Repeat (constPropArith e v) (constProp c1 $0)
    (* Again, because analyzing loops is beyond our intentions, we reset
     * knowledge to empty as we descend into the loop body. *)
  end.

(* You may remember this helpful lemma from class.
 * It's likely to come in handy again here. *)
Lemma selfCompose_extensional : forall {A} (f g : A -> A) n x,
  (forall y, f y = g y)
  -> selfCompose f n x = selfCompose g n x.
Proof.
  induct n; simplify; try equality.

  rewrite H.
  apply IHn.
  trivial.
Qed.

(* Finally, we come to your task: prove this fact. *)
Definition whatToProve := forall (c : cmd) (v1 v2 : valuation),
  (* [v1] captures compile-time knowledge of variable values,
   * while [v2] captures the full runtime knowledge.
   * The premise here captures that [v1] includes a subset of the mappings known
   * in [v2]. *)
  (forall x n, v1 $? x = Some n -> v2 $? x = Some n)
  (* Given that premise, we conclude that constant propagation doesn't change
   * the semantics of commands. *)
  -> exec (constProp c v1) v2 = exec c v2.
