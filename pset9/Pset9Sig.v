(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 9 *)

Require Import Frap.

(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)

Set Implicit Arguments.
Set Asymmetric Patterns.


(* In this pset, we explore yet another extension of the mixed-embedding Hoare
 * logic from lecture: recursive functions, where each function is associated
 * with a precondition and postcondition. *)

(* First, let's duplicate some definitions from the lecture code. *)

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).
Definition heap := fmap nat nat.
Definition assertion := heap -> Prop.

Hint Extern 1 (_ <= _) => linear_arithmetic.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic.

Ltac simp := repeat (simplify; subst; propositional;
                    try match goal with
                        | [ H : ex _ |- _ ] => invert H
                        end); try linear_arithmetic.

Inductive loop_outcome acc :=
| Done (a : acc)
| Again (a : acc).

(* Now here's our expanded [cmd] type. *)
Inductive cmd : Set -> Type :=
| Return {result : Set} (r : result) : cmd result
| Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Read (a : nat) : cmd nat
| Write (a v : nat) : cmd unit
| Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc
| Fail {result} : cmd result

| Call (func : string) (arg : nat) : cmd nat.
(* Here's the one extra constructor.  We only allow functions that take single
 * arguments, which must be numeric, and which return numbers. *)

(* Same syntactic sugar for commands as in lecture: *)
Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).

(* Now to define a small-step interpreter.  We reuse the result type from
 * lecture. *)
Inductive stepResult (result : Set) :=
| Answer (r : result)
| Stepped (h : heap) (c : cmd result)
| Failed.

Implicit Arguments Failed [result].

(* New ingredient: *)
Definition funcs := fmap string (nat -> cmd nat).
(* A value of type [funcs] gives the definitions of all available functions.
 * Each function's name is mapped to a body, represented as a Coq function over
 * the actual parameter value. *)

Fixpoint step (fs : funcs) {result} (c : cmd result) (h : heap) : stepResult result :=
  match c with
  | Return _ r => Answer r
  | Bind _ _ c1 c2 =>
    match step fs c1 h with
    | Answer r => Stepped h (c2 r)
    | Stepped h' c1' => Stepped h' (Bind c1' c2)
    | Failed => Failed
    end
  | Read a => Answer (h $! a)
  | Write a v => Stepped (h $+ (a, v)) (Return tt)
  | Loop _ init body =>
    Stepped h (r <- body init;
               match r with
               | Done r' => Return r'
               | Again r' => Loop r' body
               end)
  | Fail _ => Failed

  (* New case for function calls: try to step to the function body, failing if
   * the function is not actually defined in [fs]. *)
  | Call f x =>
    match fs $? f with
    | None => Failed
    | Some body => Stepped h (body x)
    end
  end.

Fixpoint multiStep (fs : funcs) {result} (c : cmd result) (h : heap) (n : nat) : stepResult result :=
  match n with
  | O => Stepped h c
  | S n' => match step fs c h with
            | Answer r => Answer r
            | Stepped h' c' => multiStep fs c' h' n'
            | Failed => Failed
            end
  end.

(* New ingredient for stating Hoare triples: *)
Definition funcspecs := fmap string (nat -> assertion * (nat -> assertion)).
(* Each function is mapped to its precondition and postcondition, respectively,
 * which are allowed to refer to the actual parameter value, passed as the [nat]
 * argument shown above.  Recall that postconditions are functions from return
 * values to assertions, hence the nested [nat] parameter above. *)

(* Now we add a [funcspecs] called [fsp] as a parameter to the verification
 * predicate, and we add a new rule for [Call]. *)
Inductive hoare_triple (fsp : funcspecs) : assertion -> forall {result}, cmd result -> (result -> assertion) -> Prop :=
| HtReturn : forall P {result : Set} (v : result),
    hoare_triple fsp P (Return v) (fun r h => P h /\ r = v)
| HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
    hoare_triple fsp P c1 Q
    -> (forall r, hoare_triple fsp (Q r) (c2 r) R)
    -> hoare_triple fsp P (Bind c1 c2) R
| HtRead : forall P a,
    hoare_triple fsp P (Read a) (fun r h => P h /\ r = h $! a)
| HtWrite : forall P a v,
    hoare_triple fsp P (Write a v) (fun _ h => exists h', P h' /\ h = h' $+ (a, v))

| HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) I,
    (forall acc, hoare_triple fsp (I (Again acc)) (body acc) I)
    -> hoare_triple fsp (I (Again init)) (Loop init body) (fun r h => I (Done r) h)

| HtFail : forall {result},
    hoare_triple fsp (fun _ => False) (Fail (result := result)) (fun _ _ => False)

(* The new rule! *)
| HtCall : forall f x sp (P P' : assertion) Q,
    fsp $? f = Some sp
    (* Look up [f] in the function-specs dictionary, to get the spec [sp]. *)

    -> sp x = (P', Q)
    (* Specialize the spec to the actual parameter [x], to get precondition [P']
     * and postcondition [Q]. *)

    -> (forall h, P h -> P' h)
    (* Check that the current precondition implies the function's
     * precondition. *)

    -> hoare_triple fsp P (Call f x) (fun r h => (exists h', P h') /\ Q r h)
    (* Conclude that the current precondition is sufficient for the call.  The
     * postcondition extends the function's postcondition with a memory that the
     * original precondition also held at some point in the past. *)

| HtConsequence : forall {result} (c : cmd result) P Q (P' : assertion) (Q' : _ -> assertion),
    hoare_triple fsp P c Q
    -> (forall h, P' h -> P h)
    -> (forall r h, Q r h -> Q' r h)
    -> hoare_triple fsp P' c Q'.

(* The Hoare-triple syntax is extended with the function-specs-dictionary
 * [fsp]. *)
Notation "fsp ||- {{ h ~> P }} c {{ r & h' ~> Q }}" :=
  (hoare_triple fsp (fun h => P) c (fun r h' => Q)) (at level 70, c at next level).

(* What does it mean for a [funcspecs] to be compatible with a [funcs]? *)
Definition funcspecs_ok (fsp : funcspecs) (fs : funcs) :=
  forall f,
    match fsp $? f with
    | None => True
      (* No condition imposed for a function not included in [fsp]. *)

    | Some sp => match fs $? f with
                 | None => False
                   (* However, if a function is in [fsp], it *must* be in [fs],
                    * too.  Otherwise [hoare_triple] would let us call a
                    * function that doesn't exist! *)

                 | Some body =>
                   (* Consider all possible arguments [x], and get the
                    * associated precondition [P] and postcondition [Q] for
                    * each. *)
                   forall x, let (P, Q) := sp x in
                             hoare_triple fsp P (body x) Q
                             (* The body had better satisfy them, when we
                              * instantiate it with the argument [x].  Note that
                              * we may verify the body against the very same
                              * [fsp] that we started with, which allows
                              * recursion.  There is an interesting connection
                              * here with out strengthened invariant to prove
                              * type safety for lambda calculus with
                              * references. *)
                 end
    end.

Notation "fsp ||-- fs" :=
  (funcspecs_ok fsp fs) (at level 70).

(* Now we have lemma and tactics imported from lecture.  It's safe to skip ahead
 * to the text "Example programs". *)

Lemma HtStrengthen : forall fsp {result} (c : cmd result) P Q (Q' : _ -> assertion),
    hoare_triple fsp P c Q
    -> (forall r h, Q r h -> Q' r h)
    -> hoare_triple fsp P c Q'.
Proof.
  simplify.
  eapply HtConsequence; eauto.
Qed.

Lemma HtWeaken : forall fsp {result} (c : cmd result) P Q (P' : assertion),
    hoare_triple fsp P c Q
    -> (forall h, P' h -> P h)
    -> hoare_triple fsp P' c Q.
Proof.
  simplify.
  eapply HtConsequence; eauto.
Qed.

Ltac basic := apply HtReturn || eapply HtRead || eapply HtWrite
              || (eapply HtCall; [ simplify; reflexivity
                                 | simplify; reflexivity
                                 | ]).
Ltac step0 := basic || eapply HtBind || (eapply HtStrengthen; [ basic | ])
              || (eapply HtConsequence; [ apply HtFail | .. ]).
Ltac step := step0; simp.
Ltac ht := simp; repeat step.
Ltac conseq := simplify; eapply HtConsequence.
Ltac use_IH H := conseq; [ apply H | .. ]; ht.
Ltac loop_inv0 Inv := (eapply HtWeaken; [ apply HtLoop with (I := Inv) | .. ])
                      || (eapply HtConsequence; [ apply HtLoop with (I := Inv) | .. ]).
Ltac loop_inv Inv := loop_inv0 Inv; ht.

Definition trsys_of {result} (fs : funcs) (c : cmd result) (h : heap) := {|
  Initial := {(c, h)};
  Step := fun p1 p2 => step fs (fst p1) (snd p1) = Stepped (snd p2) (fst p2)
|}.


(** * Example programs *)

(* Here's an example to get you started verifying programs.  We'll do a pure
 * Fibonacci calculation, the naive recursive way. *)
Module fib.
  (* First, the functional program that serves as our spec *)
  Fixpoint fib (n : nat) : nat :=
    match n with
    | 0 => 1
    | S n' =>
      match n' with
      | O => 1
      | S n'' => fib n'' + fib n'
      end
    end.

  (* Now the version in our object language *)
  Definition fibonacci (n : nat) : cmd nat :=
    if n ==n 0 then
      Return 1
    else if n ==n 1 then
      Return 1
    else
      a <- Call "fibonacci" (n - 2);
      b <- Call "fibonacci" (n - 1);
      Return (a + b).

  (* We put [fibonacci] inside a dictionary of available functions. *)
  Definition fs := $0 $+ ("fibonacci", fibonacci).

  (* And here's our proof.  Note that we must establish not just the correctness
   * of a particular call to "fibonacci" but also that the function definition
   * is correct.  We quantify existentially over an appropriate specification
   * dictionary [fsp]. *)
  Theorem fibonacci_ok : exists fsp, forall n,
    fsp ||- {{_ ~> True}} Call "fibonacci" n {{r&_ ~> r = fib n}}
    /\ fsp ||-- fs.
  Proof.
    exists ($0 $+ ("fibonacci", fun n =>
                                (* [n] stands for the function formal
                                 * parameter. *)
                                  (fun _ => True,
                                   (* Precondition: anything goes! *)
                                   fun r _ => r = fib n
                                   (* Postcondition: return value is [fib n]. *)
           ))).
    propositional.
    ht.
    unfold funcspecs_ok; simplify.
    unfold fs; cases (f ==v "fibonacci"); simplify; propositional.
    unfold fibonacci.
    cases (x ==n 0); ht.
    cases (x ==n 1); ht.
    cases x; propositional.
    cases x; propositional.
    simplify.
    replace (x - 0) with x by linear_arithmetic.
    equality.
  Qed.
End fib.


(* OK, now to the program that we ask you to verify.  First, a short helper
 * function, which increments the value stored at a particular memory address. *)
Definition increment1 (n : nat) : cmd nat :=
  v <- Read (n-1);
  _ <- Write (n-1) (v+1);
  Return 0.

(* The main function: increment every memory cell with an address less than
 * [n]. *)
Definition positizer (n : nat) : cmd nat :=
  if n ==n 0 then
    Return 0
  else
    _ <- Call "increment1" n;
    Call "positizer" (n-1).

(* We put both functions in a dictionary. *)
Definition fsP := $0 $+ ("increment1", increment1) $+ ("positizer", positizer).

(* Now here's what we ask you to prove. *)
Module Type S.
  (* The positizer correctly increments all memory address below its
   * argument, or rather it ensures that all memory addresses store positive
   * values, assuming that all addresses [n] and higher already do. *)
  Axiom positizer_ok : exists fsp, forall n,
      fsp ||- {{h ~> forall i, i >= n -> h $! i > 0}}
                Call "positizer" n
              {{_&h ~> forall i, h $! i > 0}}
      /\ fsp ||-- fsP.

  (* This Hoare logic is sound. *)
  Axiom hoare_triple_sound : forall fsp fs P {result} (c : cmd result) Q,
      fsp ||-- fs
      -> hoare_triple fsp P c Q
      -> forall h, P h
                   -> invariantFor (trsys_of fs c h)
                                   (fun p => step fs (fst p) (snd p) <> Failed).

  (* To prove the second one, you probably want to copy and paste the last
   * variant of soundness proof from file DeepAndShallowEmbeddings.v that we
   * went through in lecture.  That proof is repeated multiple times in
   * different modules, and it's the version in the last module that is closest
   * to the present theorem. *)
End S.
