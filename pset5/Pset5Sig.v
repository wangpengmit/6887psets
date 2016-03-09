(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 5 *)

Require Import Frap AbstractInterpret.
(* Note that module [AbstractInterpret] here duplicates the framework
 * definitions from AbstractInterpretation.v, the file with example code from
 * the last lecture. *)

(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)


(* Though we developed an extended abstract-interpretation framework in Lab 5,
 * now we're back to the original, less precise framework.  We'll instead
 * explore another orthogonal direction: using analysis results to enable
 * *optimizations* in programs.  In outline, in this pset we will:
 * (1) Develop and verify an analysis that just tracks known constant values
 *     for variables.
 * (2) Write and verify an optimization that replaces variables with their known
 *     constant values, which is trickier than it sounds, because variables may
 *     equal different constants at different points in the code!
 * (3) Use all of the above to prove that a particular run of the optimization
 *     generates an optimized program with the same behavior as the original
 *     program. *)


(** * An abstract interpretation tracking equality to constants *)

Inductive domain :=
| Exactly (n : nat)
| Anything.

Definition binop (f : nat -> nat -> nat) (a b : domain) : domain :=
  match a, b with
  | Exactly n, Exactly m => Exactly (f n m)
  | _, _ => Anything
  end.

Definition join (a b : domain) : domain :=
  match a, b with
  | Exactly n, Exactly m => if n ==n m then Exactly n else Anything
  | _, _ => Anything
  end.

Inductive represents : nat -> domain -> Prop :=
| RepExactly : forall n,
  represents n (Exactly n)
| RepAnything : forall n,
  represents n Anything.

Hint Constructors represents.

Definition constant_absint := {|
  Top := Anything;
  Constant := Exactly;
  Add := binop plus;
  Subtract := binop Peano.minus;
  Multiply := binop mult;
  Join := join;
  Represents := represents
|}.

(* See the [Module Type] below, for the soundness theorem we ask you to prove.
 * (But its statement is completely unsurprising, given our past examples.) *)


(** * Optimizing programs based on that analysis *)

(* Our expression evaluator returns one of two outputs, for a particular input
 * expression: *)
Inductive constfold_result :=
| Known (n : nat)     (* The variable is exactly [n]. *)
| Unknown (e : arith) (* I don't know the exact value, but it's the same as this
                       * (potentially simplified) expression [e]. *).

(* It's easy to convert a result back into a normal expression. *)
Definition to_arith (r : constfold_result) : arith :=
  match r with
  | Known n => Const n
  | Unknown e => e
  end.

(* The optimizer for expressions is straightforward though a bit fiddly. *)
Fixpoint constfold_arith (e : arith) (s : astate constant_absint) : constfold_result :=
  match e with
  | Const n => Known n
  | Var x =>
    match s $? x with
    | Some (Exactly n) => Known n
    | _ => Unknown e
    end
  | Plus e1 e2 =>
    match constfold_arith e1 s, constfold_arith e2 s with
    | Known n1, Known n2 => Known (n1 + n2)
    | e1', e2' => Unknown (Plus (to_arith e1') (to_arith e2'))
    end
  | Times e1 e2 =>
    match constfold_arith e1 s, constfold_arith e2 s with
    | Known n1, Known n2 => Known (n1 * n2)
    | e1', e2' => Unknown (Times (to_arith e1') (to_arith e2'))
    end
  | Minus e1 e2 =>
    match constfold_arith e1 s, constfold_arith e2 s with
    | Known n1, Known n2 => Known (n1 - n2)
    | e1', e2' => Unknown (Minus (to_arith e1') (to_arith e2'))
    end
  end.

(* Now we get to the optimizer for commands, which is about as much code, but
 * which is significantly more intricate.  As with [absint_step], we pass a
 * parameter [wrap], standing for *the context in which this command will be
 * run.*  We also pass [ss], a map from commands to what we know about
 * variables, right before running the corresponding command.  That information
 * is enough for us to replace variable occurrences with their known constant
 * values. *)
Fixpoint constfold_cmd (c : cmd) (ss : astates constant_absint) (wrap : cmd -> cmd) : cmd :=
  match c with
  | Skip => Skip
  | Assign x e =>
    (* Note how here we query the abstract state [ss] with the wrapping of the
     * current command [c].  In other words, we are querying the analysis
     * result, asking "when we reach this command, what is known to be true
     * about the variable values?". *)
    match ss $? wrap c with
    | None => Assign x e
    | Some s => Assign x (to_arith (constfold_arith e s))
                (* What do we do with what we learn?  If there are variable
                 * values associated with this location in the program, we use
                 * them to optimize the expression being assigned. *)
    end
  | Sequence c1 c2 => Sequence (constfold_cmd c1 ss (fun c' => wrap (Sequence c' c2)))
                               (constfold_cmd c2 ss wrap)
  | If e then_ else_ =>
    If e (constfold_cmd then_ ss wrap)
         (constfold_cmd else_ ss wrap)
  | While e body =>
    While e (constfold_cmd body ss (fun c' => wrap (Sequence c' c)))
  end.

(* OK, here's a lemma that's likely to come in handy soon.
 * It says: if abstract state [s1] describes concrete state [v], and if abstract
 * state [s2] covers all cases that [s1] covers, then [s2] also describes
 * [v]. *)
Lemma compatible_subsumed : forall a (s1 s2 : astate a) v,
  compatible s1 v
  -> subsumed s1 s2
  -> compatible s2 v.
Proof.
  unfold compatible, subsumed; simplify.
  specialize (H0 x).
  cases (s1 $? x).

  apply H in Heq; first_order.

  equality.
Qed. 

Hint Resolve compatible_subsumed.

(* Here are some hints we add, to get the iteration tactics to work properly. *)

Lemma merge_astates_fok_constant : forall x : option (astate constant_absint),
  match x with Some x' => Some x' | None => None end = x.
Proof.
  simplify; cases x; equality.
Qed.

Lemma merge_astates_fok2_constant : forall x (y : option (astate constant_absint)),
    match y with
    | Some y' => Some (merge_astate x y')
    | None => Some x
    end = None -> False.
Proof.
  simplify; cases y; equality.
Qed.

Hint Resolve merge_astates_fok_constant merge_astates_fok2_constant.


(* OK, now here's what we ask you to prove! *)
Module Type S.
  Axiom constant_sound : absint_sound constant_absint.

  (* Prove: if the original program reaches some state, the optimized program
   * reaches the same state, but with the new command optimized, too.
   * The first hypothesis captures the idea that *[ss] is a correct analysis
   * result*. *)
  Axiom constfold_cmd_fwd : forall ss v c v' c',
      (forall v' c', step^* (v, c) (v', c')
                     -> exists s, ss $? c' = Some s
                                  /\ compatible s v')
      -> step^* (v, c) (v', c')
      -> step^* (v, constfold_cmd c ss (fun c1 => c1))
             (v', constfold_cmd c' ss (fun c1 => c1)).

  (* Prove (as a short corollary of the last one): if the original program runs
   * to some final state, then so does the optimized program. *)
  Axiom constfold_cmd_fwd_big : forall ss v c v',
      (forall v' c', step^* (v, c) (v', c')
                     -> exists s, ss $? c' = Some s
                                  /\ compatible s v')
      -> eval v c v'
      -> eval v (constfold_cmd c ss (fun c1 => c1)) v'.
  (* Hint: the theorems from last chapter, about equivalence of different forms
   * of operational semantics, are already imported for you here. *)
End S.

(* See the starter file Pset5.v for code to actually run your analysis to
 * justify an automatic optimization.  (You won't be graded on that part, but
 * it's satisfying to run to wrap up the assignment!) *)
