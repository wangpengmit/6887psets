(** * 6.887 Formal Reasoning About Programs - Lab 4
    * Operational Semantics *)

Require Import Frap.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)


(** Challenge 1: Nondeterminism *)

Module Challenge1.

  (* Here's the same old arithmetic-expression language. *)  
  Inductive arith : Set :=
  | Const (n : nat)
  | Var (x : var)
  | Plus (e1 e2 : arith)
  | Minus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  (* And here's the same old command language, with one twist. *)
  Inductive cmd :=
  | Skip
  | Assign (x : var) (e : arith)
  | Sequence (c1 c2 : cmd)
  | If (e : arith) (then_ else_ : cmd)
  | While (e : arith) (body : cmd)
  | Choice (c1 c2 : cmd).

  (* The last construct [Choice c1 c2] stands for a *nondeterministic choice* at
   * runtime.  Every time we reach this command, we may run either [c1] or [c2]
   * (but not both). *)

  (* Same old expression evaluation *)
  Definition valuation := fmap var nat.
  Fixpoint interp (e : arith) (v : valuation) : nat :=
    match e with
    | Const n => n
    | Var x =>
      match v $? x with
      | None => 0
      | Some n => n
      end
    | Plus e1 e2 => interp e1 v + interp e2 v
    | Minus e1 e2 => interp e1 v - interp e2 v
    | Times e1 e2 => interp e1 v * interp e2 v
    end.

  (* THE CHALLENGE IS: update each semantics with appropriate rules for
   * [Choice] and update the proofs below. *)

  (** Big-step semantics *)

  Inductive eval : valuation -> cmd -> valuation -> Prop :=
  | EvalSkip : forall v,
      eval v Skip v
  | EvalAssign : forall v x e,
      eval v (Assign x e) (v $+ (x, interp e v))
  | EvalSeq : forall v c1 v1 c2 v2,
      eval v c1 v1
      -> eval v1 c2 v2
      -> eval v (Sequence c1 c2) v2
  | EvalIfTrue : forall v e then_ else_ v',
      interp e v <> 0
      -> eval v then_ v'
      -> eval v (If e then_ else_) v'
  | EvalIfFalse : forall v e then_ else_ v',
      interp e v = 0
      -> eval v else_ v'
      -> eval v (If e then_ else_) v'
  | EvalWhileTrue : forall v e body v' v'',
      interp e v <> 0
      -> eval v body v'
      -> eval v' (While e body) v''
      -> eval v (While e body) v''
  | EvalWhileFalse : forall v e body,
      interp e v = 0
      -> eval v (While e body) v.

  (** Small-step semantics *)

  Inductive step : valuation * cmd -> valuation * cmd -> Prop :=
  | StepAssign : forall v x e,
      step (v, Assign x e) (v $+ (x, interp e v), Skip)
  | StepSeq1 : forall v c1 c2 v' c1',
      step (v, c1) (v', c1')
      -> step (v, Sequence c1 c2) (v', Sequence c1' c2)
  | StepSeq2 : forall v c2,
      step (v, Sequence Skip c2) (v, c2)
  | StepIfTrue : forall v e then_ else_,
      interp e v <> 0
      -> step (v, If e then_ else_) (v, then_)
  | StepIfFalse : forall v e then_ else_,
      interp e v = 0
      -> step (v, If e then_ else_) (v, else_)
  | StepWhileTrue : forall v e body,
      interp e v <> 0
      -> step (v, While e body) (v, Sequence body (While e body))
  | StepWhileFalse : forall v e body,
      interp e v = 0
      -> step (v, While e body) (v, Skip).

  Hint Constructors trc step eval.

  Lemma step_star_Seq : forall v c1 c2 v' c1',
    step^* (v, c1) (v', c1')
    -> step^* (v, Sequence c1 c2) (v', Sequence c1' c2).
  Proof.
    induct 1; eauto.
    cases y; eauto.
  Qed.

  Hint Resolve step_star_Seq.

  Theorem big_small : forall v c v', eval v c v'
    -> step^* (v, c) (v', Skip).
  Proof.
    induct 1; eauto 6 using trc_trans.
  Qed.

  Lemma small_big'' : forall v c v' c',
      step (v, c) (v', c')
      -> forall v'', eval v' c' v''
                     -> eval v c v''.
  Proof.
    induct 1; simplify;
    repeat match goal with
           | [ H : eval _ _ _ |- _ ] => invert1 H
           end; eauto.
  Qed.

  Hint Resolve small_big''.

  Lemma small_big' : forall v c v' c',
      step^* (v, c) (v', c')
      -> forall v'', eval v' c' v''
                     -> eval v c v''.
  Proof.
    induct 1; eauto.
    cases y; eauto.
  Qed.

  Hint Resolve small_big'.

  Theorem small_big : forall v c v',
      step^* (v, c) (v', Skip)
      -> eval v c v'.
  Proof.
    eauto.
  Qed.

  (** Contextual small-step semantics *)

  Inductive context :=
  | Hole
  | CSeq (C : context) (c : cmd).

  Inductive plug : context -> cmd -> cmd -> Prop :=
  | PlugHole : forall c, plug Hole c c
  | PlugSeq : forall c C c' c2,
      plug C c c'
      -> plug (CSeq C c2) c (Sequence c' c2).

  Inductive step0 : valuation * cmd -> valuation * cmd -> Prop :=
  | Step0Assign : forall v x e,
      step0 (v, Assign x e) (v $+ (x, interp e v), Skip)
  | Step0Seq : forall v c2,
      step0 (v, Sequence Skip c2) (v, c2)
  | Step0IfTrue : forall v e then_ else_,
      interp e v <> 0
      -> step0 (v, If e then_ else_) (v, then_)
  | Step0IfFalse : forall v e then_ else_,
      interp e v = 0
      -> step0 (v, If e then_ else_) (v, else_)
  | Step0WhileTrue : forall v e body,
      interp e v <> 0
      -> step0 (v, While e body) (v, Sequence body (While e body))
  | Step0WhileFalse : forall v e body,
      interp e v = 0
      -> step0 (v, While e body) (v, Skip).

  Inductive cstep : valuation * cmd -> valuation * cmd -> Prop :=
  | CStep : forall C v c v' c' c1 c2,
      plug C c c1
      -> step0 (v, c) (v', c')
      -> plug C c' c2
      -> cstep (v, c1) (v', c2).

  Hint Constructors plug step0 cstep.

  Theorem step_cstep : forall v c v' c',
    step (v, c) (v', c')
    -> cstep (v, c) (v', c').
  Proof.
    induct 1; repeat match goal with
                     | [ H : cstep _ _ |- _ ] => invert H
                     end; eauto.
  Qed.

  Hint Resolve step_cstep.

  Lemma step0_step : forall v c v' c',
    step0 (v, c) (v', c')
    -> step (v, c) (v', c').
  Proof.
    induct 1; eauto.
  Qed.

  Hint Resolve step0_step.

  Lemma cstep_step' : forall C c0 c,
    plug C c0 c
    -> forall v' c'0 v c', step0 (v, c0) (v', c'0)
    -> plug C c'0 c'
    -> step (v, c) (v', c').
  Proof.
    induct 1; simplify; repeat match goal with
                               | [ H : plug _ _ _ |- _ ] => invert1 H
                               end; eauto.
  Qed.

  Hint Resolve cstep_step'.

  Theorem cstep_step : forall v c v' c',
    cstep (v, c) (v', c')
    -> step (v, c) (v', c').
  Proof.
    induct 1; eauto.
  Qed.

End Challenge1.


(** Challenge 2: Functions and Control Stack *)

(* This time, we give you the new semantics and ask you to fill in the
 * proofs. *)

Module Challenge2.
  
  Inductive arith : Set :=
  | Const (n : nat)
  | Var (x : var)
  | Plus (e1 e2 : arith)
  | Minus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  Definition valuation := fmap var nat.
  
  (* The new twist this time: function calls! *)
  Inductive cmd :=
  | Skip
  | Assign (x : var) (e : arith)
  | Sequence (c1 c2 : cmd)
  | If (e : arith) (then_ else_ : cmd)
  | While (e : arith) (body : cmd)

  | Call (lhs f : var) (arg : arith)
  (* Calling the function named [f] with the argument [arg], assigning the
   * return value to [lhs] *)

  | InCall (v : valuation) (lhs ret : var) (c : cmd).
  (* This other command form only arises in the course of small-step evaluation.
   * It means that a call to a function was made from a context with valuation
   * [v], waiting to assign the return value to variable [lhs].  In the called
   * function, variable [ret] is assigned to hold the return value, and we have
   * executed that function up to command [c]. *)

  Fixpoint interp (e : arith) (v : valuation) : nat :=
    match e with
    | Const n => n
    | Var x =>
      match v $? x with
      | None => 0
      | Some n => n
      end
    | Plus e1 e2 => interp e1 v + interp e2 v
    | Minus e1 e2 => interp e1 v - interp e2 v
    | Times e1 e2 => interp e1 v * interp e2 v
    end.

  (* Every function in the program is mapped to one of these. *)
  Record fun_spec := {
    Arg : var; (* Name of formal parameter *)
    Ret : var; (* Variable where return value must be stored *)
    Body : cmd (* Body to execute upon call *)
  }.

  (** An environment is a mapping from function names to function specs. *)
  Definition environment := fmap var fun_spec.

  Section env.

    Variable env : environment.
    
    (** Big-step semantics *)
    Inductive eval : valuation -> cmd -> valuation -> Prop :=
    | EvalSkip : forall v,
        eval v Skip v
    | EvalAssign : forall v x e,
        eval v (Assign x e) (v $+ (x, interp e v))
    | EvalSeq : forall v c1 v1 c2 v2,
        eval v c1 v1
        -> eval v1 c2 v2
        -> eval v (Sequence c1 c2) v2
    | EvalIfTrue : forall v e then_ else_ v',
        interp e v <> 0
        -> eval v then_ v'
        -> eval v (If e then_ else_) v'
    | EvalIfFalse : forall v e then_ else_ v',
        interp e v = 0
        -> eval v else_ v'
        -> eval v (If e then_ else_) v'
    | EvalWhileTrue : forall v e body v' v'',
        interp e v <> 0
        -> eval v body v'
        -> eval v' (While e body) v''
        -> eval v (While e body) v''
    | EvalWhileFalse : forall v e body,
        interp e v = 0
        -> eval v (While e body) v

    | EvalCall : forall v lhs f arg spec v',
        env $? f = Some spec 
        (* When making a function call, look up the function spec by name. *)

        -> eval ($0 $+ (spec.(Arg), interp arg v)) spec.(Body) v'
        (* Then evaluate the callee's body, in a valuation with just the actual
         * parameter value. *)

        -> eval v (Call lhs f arg) (v $+ (lhs, interp (Var spec.(Ret)) v'))
        (* Extend the original valuation with the function return value. *)

    | EvalInCall : forall v0 lhs ret v c v',
        eval v c v'
        -> eval v (InCall v0 lhs ret c) (v0 $+ (lhs, interp (Var ret) v')).
        (* This [InCall] case is just to make the proofs below go through nicely.
         * We don't actually need [InCall] for big-step evaluation. *)

    (** Small-step semantics *)

    Inductive step : valuation * cmd -> valuation * cmd -> Prop :=
    | StepAssign : forall v x e,
        step (v, Assign x e) (v $+ (x, interp e v), Skip)
    | StepSeq1 : forall v c1 c2 v' c1',
        step (v, c1) (v', c1')
        -> step (v, Sequence c1 c2) (v', Sequence c1' c2)
    | StepSeq2 : forall v c2,
        step (v, Sequence Skip c2) (v, c2)
    | StepIfTrue : forall v e then_ else_,
        interp e v <> 0
        -> step (v, If e then_ else_) (v, then_)
    | StepIfFalse : forall v e then_ else_,
        interp e v = 0
        -> step (v, If e then_ else_) (v, else_)
    | StepWhileTrue : forall v e body,
        interp e v <> 0
        -> step (v, While e body) (v, Sequence body (While e body))
    | StepWhileFalse : forall v e body,
        interp e v = 0
        -> step (v, While e body) (v, Skip)

    | StepStartCall : forall v lhs f arg spec,
        env $? f = Some spec
        -> step (v, Call lhs f arg) ($0 $+ (spec.(Arg), interp arg v), InCall v lhs spec.(Ret) spec.(Body))
        (* To begin with a function call, step to an [InCall], in a fresh
         * valuation containing only the actual parameter value.  Remember the
         * current valuation as an argument to [InCall]. *)

    | StepInCall : forall v c v' c' v0 lhs ret,
        step (v, c) (v', c')
        -> step (v, InCall v0 lhs ret c) (v', InCall v0 lhs ret c')
        (* Basic congruence rule, for stepping with an [InCall], meaning that
         * we take a step in the function that was called, leaving alone the
         * "call stack" around it. *)

    | StepEndCall : forall v0 lhs ret v,
        step (v, InCall v0 lhs ret Skip) (v0, Assign lhs (Const (interp (Var ret) v))).
        (* When does our [InCall] detour end?  When the callee's body has
         * stepped to [Skip].  Then we back up and assign to the caller's
         * variable that has been waiting to receive the return value. *)

    Theorem big_small : forall v c v',
        eval v c v'
        -> step^* (v, c) (v', Skip).
    Proof.
    Admitted.

    Theorem small_big : forall v c v',
        step^* (v, c) (v', Skip)
        -> eval v c v'.
    Proof.
    Admitted.

    (** Small-step semantics with control stack *)

    (* As an alternative to evaluation contexts, we can also use an explicit
     * representation of a call stack.  First, a basic step relation that
     * doesn't need a call stack. *)

    Inductive step0 : valuation * cmd -> valuation * cmd -> Prop :=
    | Step0Assign : forall v x e,
        step0 (v, Assign x e) (v $+ (x, interp e v), Skip)
    | Step0IfTrue : forall v e then_ else_,
        interp e v <> 0
        -> step0 (v, If e then_ else_) (v, then_)
    | Step0IfFalse : forall v e then_ else_,
        interp e v = 0
        -> step0 (v, If e then_ else_) (v, else_)
    | Step0WhileTrue : forall v e body,
        interp e v <> 0
        -> step0 (v, While e body) (v, Sequence body (While e body))
    | Step0WhileFalse : forall v e body,
        interp e v = 0
        -> step0 (v, While e body) (v, Skip).

    (* Our call stack will be a sequence of frames like these. *)
    Record frame := {
      Val : valuation; (* Local variable values *)
      Cont : cmd;      (* Command waiting to run after called function
                        * returns *)
      LHS : var;       (* Variable waiting to receive return value of called
                        * function *)
      RetVar : var     (* Place to store return value of this function *)
    }.

    Definition stack := list frame.

    (* What are the four components of states in this semantics?
     * #1: call stack
     * #2: local variables of topmost call
     * #3: command to run next
     * #4: additional command to run afterward, called the *continuation* *)
    Inductive stepcs : stack * valuation * cmd * cmd -> stack * valuation * cmd * cmd -> Prop :=

    (* Easy case: just step the main command as usual *)
    | StepcsStep0 : forall v c v' c' s k,
        step0 (v, c) (v', c') ->
        stepcs (s, v, c, k) (s, v', c', k)

    (* Fancier case: when encountering a sequence, pop off its second step and
     * push it onto the front of the continuation. *)
    | StepcsSeq : forall s v c1 c2 k,
        stepcs (s, v, Sequence c1 c2, k) (s, v, c1, Sequence c2 k)

    (* Natural companion to last rule: when the main command is empty, start
     * running the next command of the continuation, if one is available. *)
    | StepcsCont : forall s v k1 k2,
        stepcs (s, v, Skip, Sequence k1 k2) (s, v, k1, k2)

    (* When both the main command and the continuation are [Skip], we're done
     * running this function.  Time to pop the call stack and return to the
     * caller. *)
    | StepcsReturn : forall fr s v,
        stepcs (fr :: s, v, Skip, Skip) (s, fr.(Val) $+ (fr.(LHS), interp (Var fr.(RetVar)) v), Skip, fr.(Cont))

    (* To make a cal, push a new frame onto the call stack. *)
    | StepcsCall : forall s v lhs f arg k spec,
        env $? f = Some spec
        -> stepcs (s, v, Call lhs f arg, k) ({| Val := v; Cont := k; LHS := lhs; RetVar := spec.(Ret)|} :: s, $0 $+ (spec.(Arg), interp arg v), spec.(Body), Skip)

    (* We don't actually need [InCall] in this semantics, but here's a single
     * step to get rid of it. *)
    | StepcsInCall : forall s v0 lhs ret v c k,
        stepcs (s, v, InCall v0 lhs ret c, k) ({| Val := v0; Cont := k; LHS := lhs; RetVar := ret|} :: s, v, c, Skip).
    
    Theorem eval_stepcs : forall v c v',
        eval v c v'
        -> stepcs^* ([], v, c, Skip) ([], v', Skip, Skip).
    Proof.
    Admitted.

    Theorem stepcs_eval : forall v c v',
        stepcs^* ([], v, c, Skip) ([], v', Skip, Skip)
        -> eval v c v'.
    Proof.
    Admitted.

  End env.

End Challenge2.

(* CHALLENGE #3: Extend the language with an explicit "return" command and add
 * one rule to the control-stack semantics to explain its effect.
 * The other semantics styles would need bigger modifications to handle
 * "return," so here we see an advantage of the control-stack formulation. *)
