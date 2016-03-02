(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 4 *)

Require Import Frap.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)


(* In Lab 4, we saw a few ways to model function calls with operational
 * semantics.  In this problem set, we extend the picture with *exceptions*,
 * including their interactions with function calls.  But first, the same old
 * boring language of expressions. *)

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Definition valuation := fmap var nat.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd)
| While (e : arith) (body : cmd)
| Call (lhs f : var) (arg : arith)
| InCall (v : valuation) (lhs ret : var) (c : cmd)

(* The new cases: *)

| Try (try : cmd) (exn : var) (handler : cmd)
(* Run [try].  If it throws an uncaught exception, switch to running [handler],
 * with variable [exn] bound to the exception that was thrown. *)

| Throw (e : arith).
(* Abort normal execution, throwing the value of [e]. *)

(* Boring old expression interpreter *)
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

(* Function specifications, as in the lab *)
Record fun_spec := {
  Arg : var;
  Ret : var;
  Body : cmd
}.

Definition environment := fmap var fun_spec.

(* To describe the results of our big-step semantics, we need this new type. *)
Inductive outcome :=
| Normal
  (* Execution finished normally. *)

| Exception (exn : nat).
  (* Execution finished with this uncaught exception.
   * Note that our exceptions are numbers, since our expressions all evaluate to
   * numbers. *)

Section env.

  Variable env : environment.
  
  (** Big-step semantics *)
  Inductive eval : valuation -> cmd -> outcome * valuation -> Prop :=
  | EvalSkip : forall v,
      eval v Skip (Normal, v)
    (* Note that the old rules tend to return [Normal] values. *)
  | EvalAssign : forall v x e,
      eval v (Assign x e) (Normal, v $+ (x, interp e v))
  | EvalSeq : forall v c1 v1 c2 ov2,
      eval v c1 (Normal, v1)
      -> eval v1 c2 ov2
      -> eval v (Sequence c1 c2) ov2
    (* However, this rule passes along whatever is the outcome [ov2] of the
     * second command, be it normal or exceptional. *)
  | EvalSeqExn : forall v c1 exn v1 c2,
      eval v c1 (Exception exn, v1)
      -> eval v (Sequence c1 c2) (Exception exn, v1)
    (* This second [Seq] rule handles the case where the first command raises an
     * exception. *)
  | EvalIfTrue : forall v e then_ else_ ov',
      interp e v <> 0
      -> eval v then_ ov'
      -> eval v (If e then_ else_) ov'
  | EvalIfFalse : forall v e then_ else_ ov',
      interp e v = 0
      -> eval v else_ ov'
      -> eval v (If e then_ else_) ov'
  | EvalWhileTrue : forall v e body v' ov'',
      interp e v <> 0
      -> eval v body (Normal, v')
      -> eval v' (While e body) ov''
      -> eval v (While e body) ov''
  | EvalWhileTrueExn : forall v e body exn v',
      interp e v <> 0
      -> eval v body (Exception exn, v')
      -> eval v (While e body) (Exception exn, v')
  | EvalWhileFalse : forall v e body,
      interp e v = 0
      -> eval v (While e body) (Normal, v)

  | EvalCall : forall v lhs f arg spec v',
      env $? f = Some spec 
      -> eval ($0 $+ (spec.(Arg), interp arg v)) spec.(Body) (Normal, v')
      -> eval v (Call lhs f arg) (Normal, v $+ (lhs, interp (Var spec.(Ret)) v'))
  | EvalCallExn : forall v lhs f arg spec exn v',
      env $? f = Some spec 
      -> eval ($0 $+ (spec.(Arg), interp arg v)) spec.(Body) (Exception exn, v')
      -> eval v (Call lhs f arg) (Exception exn, v)
    (* Note the crucial difference between the two [EvalCall] rules: with a
     * normal outcome (other rule) of the called function, we extend the
     * valuation with the return value.  In case of an exception (this rule), we
     * leave the valuation alone. *)

  | EvalTry : forall v c v' x handler,
      eval v c (Normal, v')
      -> eval v (Try c x handler) (Normal, v')
    (* Normal evaluation of a [try] body bubbles out of the [try]. *)

  | EvalTryExn : forall v c exn v' x handler ov'',
      eval v c (Exception exn, v')
      -> eval (v' $+ (x, exn)) handler ov''
      -> eval v (Try c x handler) ov''
    (* Exceptional evaluation of the body switches to running the handler. *)

  | EvalThrow : forall v e,
      eval v (Throw e) (Exception (interp e v), v)
    (* Throwing generates the expected exceptional outcome. *)

  | EvalInCall : forall v0 lhs ret v c v',
      eval v c (Normal, v')
      -> eval v (InCall v0 lhs ret c) (Normal, v0 $+ (lhs, interp (Var ret) v'))
  | EvalInCallExn : forall v0 lhs ret v c exn v',
      eval v c (Exception exn, v')
      -> eval v (InCall v0 lhs ret c) (Exception exn, v0).
    (* Finally, two goofy rules just to make this semantics complete for
     * [InCall], which we really only need for the small-step semantics. *)

  (** Small-step semantics *)

  Inductive step : valuation * cmd -> valuation * cmd -> Prop :=
  | StepAssign : forall v x e,
      step (v, Assign x e) (v $+ (x, interp e v), Skip)
  | StepSeq1 : forall v c1 c2 v' c1',
      step (v, c1) (v', c1')
      -> step (v, Sequence c1 c2) (v', Sequence c1' c2)
  | StepSeq2 : forall v c2,
      step (v, Sequence Skip c2) (v, c2)
  | StepSeqThrow : forall v (n : nat) c2,
      step (v, Sequence (Throw (Const n)) c2) (v, Throw (Const n))
    (* Note how a [Throw] can bubble up from the first part of a sequence. *)
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
  | StepInCall : forall v c v' c' v0 lhs ret,
      step (v, c) (v', c')
      -> step (v, InCall v0 lhs ret c) (v', InCall v0 lhs ret c')
  | StepEndCall : forall v0 lhs ret v,
      step (v, InCall v0 lhs ret Skip) (v0, Assign lhs (Const (interp (Var ret) v)))
  | StepEndCallThrow : forall v0 lhs ret v (n : nat),
      step (v, InCall v0 lhs ret (Throw (Const n))) (v0, Throw (Const n))
    (* Here we also see a [Throw] bubble up out of a call.  That is, the
     * callee's uncaught exceptions escape to the caller. *)
  | StepTry : forall v c v' c' x handler,
      step (v, c) (v', c')
      -> step (v, Try c x handler) (v', Try c' x handler)
  | StepTryDone : forall v x handler,
      step (v, Try Skip x handler) (v, Skip)
  | StepTryThrow : forall v (n : nat) x handler,
      step (v, Try (Throw (Const n)) x handler) (v $+ (x, n), handler)
    (* Exceptions also bubble out of [Try]s, but they go to the handler instead
     * of to other surrounding code.  (Of course, if the handler raises another
     * exception, the adventure continues.) *)
  | StepThrow : forall v (e : arith),
      (forall n : nat, e <> Const n)
      -> step (v, Throw e) (v, Throw (Const (interp e v))).
    (* If throwing an expression that isn't fully evaluated, evaluate it before
     * continuing. *)

   (* Notice how the small-step style was more convenient to update in some
    * places.  We didn't need to create dual versions of as many rules, for
    * the normal and exceptional cases.  On the other hand, the "bubbling" rules
    * make up for it, so we get just as many rules. *)

   (* See the bottom of this file for the theorems we ask you to prove about
    * these semantics. *)

  (** Small-step semantics with control stack *)

  (* Now we take the same step that we finished up with in the lab. *)

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
      -> step0 (v, While e body) (v, Skip)
  | Step0Throw : forall v (e : arith),
      (forall n : nat, e <> Const n)
      -> step0 (v, Throw e) (v, Throw (Const (interp e v))).
    (* This last rule is the one new one vs. the lab.  It's pretty similar to
     * the last rule of the basic small-step semantics. *)

  (* Call frames: just as in the lab, with a different name *)
  Record call_frame := {
    Val : valuation;
    Cont : cmd;
    LHS : var;
    RetVar : var
  }.

  (* However, now our control stacks have *two* kinds of frames!
   * The other represents a pending exception handler. *)
  Record handler_frame := {
    ExnVar : var;  (* In case of uncaught exception, save it to this
                    * variable... *)
    Handler : cmd; (* ...and commence running this command. *)
    ExnCont : cmd  (* Afterward, run this command. *)
  }.

  Inductive frame :=
  | CallFrame (fr : call_frame)
  | HandlerFrame (fr : handler_frame).

  Definition stack := list frame.

  (* Now we proceed much as in the lab. *)
  Inductive stepcs : stack * valuation * cmd * cmd -> stack * valuation * cmd * cmd -> Prop :=
  | StepcsStep0 : forall v c v' c' s k,
      step0 (v, c) (v', c') ->
      stepcs (s, v, c, k) (s, v', c', k)
  | StepcsSeq : forall s v c1 c2 k,
      stepcs (s, v, Sequence c1 c2, k) (s, v, c1, Sequence c2 k)
  | StepcsCont : forall s v k1 k2,
      stepcs (s, v, Skip, Sequence k1 k2) (s, v, k1, k2)
  | StepcsReturn : forall fr s v,
      stepcs (CallFrame fr :: s, v, Skip, Skip) (s, fr.(Val) $+ (fr.(LHS), interp (Var fr.(RetVar)) v), Skip, fr.(Cont))

  | StepcsReturnHandlerFrame : forall fr s v,
      stepcs (HandlerFrame fr :: s, v, Skip, Skip) (s, v, Skip, fr.(ExnCont))
    (* When a command finishes normally and there is a pending exception
     * handler, tell that handler "Sorry, Bub; not today!" and pop it off. *)

  | StepcsThrowDiscardCont : forall s v n k,
      k <> Skip ->
      stepcs (s, v, Throw (Const n), k) (s, v, Throw (Const n), Skip)
    (* When we throw an exception, discard the continuation, as we will never
     * finish normally and get around to running it. *)

  | StepcsHandleThrow : forall fr s v (n : nat),
      stepcs (HandlerFrame fr :: s, v, Throw (Const n), Skip) (s, v $+ (fr.(ExnVar), n), fr.(Handler), fr.(ExnCont))
    (* When throwing with a handler on top of the stack, pop it and start
     * running it. *)

  | StepcsThrowCallFrame : forall fr s v (n : nat),
      stepcs (CallFrame fr :: s, v, Throw (Const n), Skip) (s, fr.(Val), Throw (Const n), Skip)
    (* On the other hand, when throwing with a call frame on top, pop it and
     * jump past it to the next frame. *)

  | StepcsCall : forall s v lhs f arg k spec,
      env $? f = Some spec
      -> stepcs (s, v, Call lhs f arg, k) (CallFrame {| Val := v; Cont := k; LHS := lhs; RetVar := spec.(Ret)|} :: s, $0 $+ (spec.(Arg), interp arg v), spec.(Body), Skip)
    (* Calls proceed as before. *)

  | StepcsTry : forall s v c x handler k,
      stepcs (s, v, Try c x handler, k) (HandlerFrame {| ExnVar := x; Handler := handler; ExnCont := k|} :: s, v, c, Skip)
    (* To run a [Try], install its handler on top of the stack. *)

  | StepcsInCall : forall s v0 lhs ret v c k,
      stepcs (s, v, InCall v0 lhs ret c, k) (CallFrame {| Val := v0; Cont := k; LHS := lhs; RetVar := ret|} :: s, v, c, Skip).
    (* Same goofy [InCall] rule as before *)

End env.

Module Type S.
  Section env.
    Variable env : environment.

    Axiom big_small : forall v c v',
        eval env v c (Normal, v')
        -> (step env)^* (v, c) (v', Skip).

    Axiom big_small_exn : forall v c n v',
        eval env v c (Exception n, v')
        -> (step env)^* (v, c) (v', Throw (Const n)).

    Axiom small_big : forall v c v',
        (step env)^* (v, c) (v', Skip)
        -> eval env v c (Normal, v').

    Axiom small_big_exn : forall v c v' n,
        (step env)^* (v, c) (v', Throw (Const n))
        -> eval env v c (Exception n, v').

    Axiom eval_stepcs : forall v c v',
        eval env v c (Normal, v')
        -> (stepcs env)^* ([], v, c, Skip) ([], v', Skip, Skip).

    Axiom eval_stepcs_exn : forall v c (n : nat) v',
        eval env v c (Exception n, v')
        -> (stepcs env)^* ([], v, c, Skip) ([], v', Throw (Const n), Skip).

    Axiom stepcs_eval : forall v c v',
        (stepcs env)^* ([], v, c, Skip) ([], v', Skip, Skip)
        -> eval env v c (Normal, v').

    Axiom stepcs_eval_exn : forall v c v' (n : nat),
        (stepcs env)^* ([], v, c, Skip) ([], v', Throw (Const n), Skip)
        -> eval env v c (Exception n, v').
  End env.
End S.
