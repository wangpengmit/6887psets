(** * 6.887 Formal Reasoning About Programs - Lab 11
    * Partial Reduction for Shared-Memory Concurrency *)

Require Import Frap.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)

Set Implicit Arguments.
Set Asymmetric Patterns.

(* In this lab we will manually (without using a model checker) verify some programs using both
   the original step relation and the optimized step relation by partial reduction and 
   commutativity, to experience the reduction in state space. *)

(* BEGIN: copy from lecture code *)
Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).
Definition heap := fmap nat nat.

Hint Extern 1 (_ <= _) => linear_arithmetic.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic.

Inductive cmd :=
| Return (r : nat)
| Bind (c1 : cmd) (c2 : nat -> cmd)
| Read (a : nat)
| Write (a v : nat)
| Fail
| Par (c1 c2 : cmd)
| Lock (a : nat)
| Unlock (a : nat).

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Infix "||" := Par.

Definition locks := set nat.

Inductive step : heap * locks * cmd -> heap * locks * cmd -> Prop :=
| StepBindRecur : forall c1 c1' c2 h h' l l',
  step (h, l, c1) (h', l', c1')
  -> step (h, l, Bind c1 c2) (h', l', Bind c1' c2)
| StepBindProceed : forall v c2 h l,
  step (h, l, Bind (Return v) c2) (h, l, c2 v)
| StepRead : forall h l a,
  step (h, l, Read a) (h, l, Return (h $! a))
| StepWrite : forall h l a v,
  step (h, l, Write a v) (h $+ (a, v), l, Return 0)
| StepParRecur1 : forall h l c1 c2 h' l' c1',
  step (h, l, c1) (h', l', c1')
  -> step (h, l, Par c1 c2) (h', l', Par c1' c2)
| StepParRecur2 : forall h l c1 c2 h' l' c2',
  step (h, l, c2) (h', l', c2')
  -> step (h, l, Par c1 c2) (h', l', Par c1 c2')
| StepLock : forall h l a,
  ~a \in l
  -> step (h, l, Lock a) (h, l \cup {a}, Return 0)
| StepUnlock : forall h l a,
  a \in l
  -> step (h, l, Unlock a) (h, l \setminus {a}, Return 0).

Fixpoint notAboutToFail (c : cmd) : bool :=
  match c with
  | Fail => false
  | Bind c1 _ => notAboutToFail c1
  | Par c1 c2 => notAboutToFail c1 && notAboutToFail c2
  | _ => true
  end.

Record summary := {
  Reads : set nat;
  Writes : set nat;
  Locks : set nat
}.

Inductive summarize : cmd -> summary -> Prop :=
| SumReturn : forall r s,
    summarize (Return r) s
| SumFail : forall s,
    summarize Fail s
| SumBind : forall c1 c2 s,
    summarize c1 s
    -> (forall r, summarize (c2 r) s)
    -> summarize (Bind c1 c2) s
| SumRead : forall a s,
    a \in s.(Reads)
    -> summarize (Read a) s
| SumWrite : forall a v s,
    a \in s.(Writes)
    -> summarize (Write a v) s
| SumLock : forall a s,
    a \in s.(Locks)
    -> summarize (Lock a) s
| SumUnlock : forall a s,
    a \in s.(Locks)
    -> summarize (Unlock a) s.

Inductive summarizeThreads : cmd -> list (cmd * summary) -> Prop :=
| StPar : forall c1 c2 ss1 ss2,
    summarizeThreads c1 ss1
    -> summarizeThreads c2 ss2
    -> summarizeThreads (Par c1 c2) (ss1 ++ ss2)
| StAtomic : forall c s,
    summarize c s
    -> summarizeThreads c [(c, s)].

Inductive nextAction : cmd -> cmd -> Prop :=
| NaReturn : forall r,
    nextAction (Return r) (Return r)
| NaFail :
    nextAction Fail Fail
| NaRead : forall a,
    nextAction (Read a) (Read a)
| NaWrite : forall a v,
    nextAction (Write a v) (Write a v)
| NaLock : forall l,
    nextAction (Lock l) (Lock l)
| NaUnlock : forall l,
    nextAction (Unlock l) (Unlock l)
| NaBind : forall c1 c2 c,
    nextAction c1 c
    -> nextAction (Bind c1 c2) c.

Definition commutes (c : cmd) (s : summary) : Prop :=
  match c with
  | Return _ => True
  | Fail => True
  | Read a => ~a \in s.(Writes)
  | Write a _ => ~a \in s.(Reads) \cup s.(Writes)
  | Lock a => ~a \in s.(Locks)
  | Unlock a => ~a \in s.(Locks)
  | _ => False
  end.

Inductive stepC : heap * locks * list (cmd * summary) -> heap * locks * list (cmd * summary) -> Prop :=
| StepFirst : forall h l c h' l' c' s cs,
  step (h, l, c) (h', l', c')
  -> stepC (h, l, (c, s) :: cs) (h', l', (c', s) :: cs)
| StepAny : forall h l c h' l' s cs1 c1 s1 cs2 c1',
  (forall c0 h'' l'' c'', nextAction c c0
                          -> List.Forall (fun c_s => commutes c0 (snd c_s)) (cs1 ++ (c1, s1) :: cs2)
                          -> step (h, l, c) (h'', l'', c'')
                          -> False)
  -> step (h, l, c1) (h', l', c1')
  -> stepC (h, l, (c, s) :: cs1 ++ (c1, s1) :: cs2) (h', l', (c, s) :: cs1 ++ (c1', s1) :: cs2).

(* END: copy of lecture code *)

(* Here is our first example program, two threads manipulating their own memory addresses without interfering with each other. *)

Definition independent_th n :=
  _ <- Write n 2;
  a <- Read n;
  if a ==n 2 then
    Return 0
  else
    Fail.
  
Example independent :=
  independent_th 0 || independent_th 1.

(** * Challenge 1: *)
(** Prove that [independent] won't fail, without using the model checker. The proof will be a long and tedious list of [invert]s, so you don't need to finish the proof. Just get a sense of the exponential explosion of paths you need to explore. *)
Theorem independent_no_fail : forall h l c, step^* ($0, {}, independent) (h, l, c) -> notAboutToFail c = true.
Proof.
Admitted.

(** * Challenge 2: *)
(** Define a summary of the [independent] program and prove that it's really an accurate summary. *)
Definition independent_summary : list (cmd * summary) := [].

Theorem summarize_independent : summarizeThreads independent independent_summary.
Proof.
Admitted.

(** * Challenge 3: *)
(** Prove that [independent_summary] won't fail, without using the model checker. This time the exploration space should be much more manageable. *)
Theorem independent_summary_no_fail : forall h l cs, stepC^* ($0, {}, independent_summary) (h, l, cs) -> forallb (fun c_s => notAboutToFail (fst c_s)) cs = true.
Proof.
Admitted.

(* Here is our second example program, to show that when the program has a bug, the optimized step relation can catch it, so the reduced state space won't miss bugs. *)

Example buggy :=
  (a <- Read 0;
   _ <- Write 1 (a + 1);
   a <- Read 1;
   if a ==n 0 then
     Return 0
   else
     Fail)
  || (b <- Read 2;
       Write 2 (b + 1)).

(** * Challenge 4: *)
(** Show that there is a bug in program [buggy]. *)
Theorem buggy_fail : exists h l c, step^* ($0, {}, buggy) (h, l, c) /\ notAboutToFail c = false.
Proof.
Admitted.

(** * Challenge 5: *)
(** Define a summary of the [buggy] program and prove that it's really an accurate summary. *)
Definition buggy_summary : list (cmd * summary) := [].

Theorem summarize_buggy : summarizeThreads buggy buggy_summary.
Proof.
Admitted.

(** * Challenge 6: *)
(** Show that there is also a bug in [buggy_summary], using the optimized step relation. *)
Theorem buggy_summary_fail : exists h l cs, stepC^* ($0, {}, buggy_summary) (h, l, cs) /\ Exists (fun c_s => notAboutToFail (fst c_s) = false) cs.
Proof.
Admitted.
