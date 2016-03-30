(** * 6.887 Formal Reasoning About Programs - Lab 7
    * Linear Types *)

Require Import Frap.
Require Import Classical. (* Classical lets us compare two terms of any type,
                           * which simplifies the proof. *)

Ltac compare_for_equality e1 e2 := destruct (classic (e1 = e2)); subst; simplify; try equality.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)

(** * Linear Types *)

(* The references type system presented in lecture keeps track of allocated
 * memory cells but doesn't keep track of "freed" cells (actually it doesn't
 * even allow freeing).  *Linear types* provide more precise control of memory
 * (and other resource) usage.  In a linear type system, each constructed object
 * can and must be used exactly once.  After it's used, it is considered
 * *consumed* and can't be used again.  There cannot be "double freeing", where
 * an object is consumed twice; nor can there be any "dangling object", an
 * object that is unused but can't be mentioned anymore.
 *
 * To statically guarantee these properties, the main idea of linear type
 * systems is to treat each variable in the typing context (i.e. static scoping
 * context) as a resource floating around that's available to use, and once that
 * variable is mentioned in an expression, it is considered *consumed* and
 * removed from the typing context (i.e. goes out of scope).  Additionally, for
 * an expression to be well-typed against a typing context, the expression must
 * use up all the variables in the context.  There cannot be any extra variables
 * left behind.  (Cue bad joke about "no man left behind!" in classic war
 * movies.)
 * 
 * Let's define a linear type system and prove it sound.  We recommend
 * consulting book source file TypesAndMutation.v for the self-contained proof
 * of the type system for mutable references without deallocation, which has
 * much in common with this new proof. *)

Notation loc := nat.

Inductive exp : Set :=
| Var (x : var)
| Const (b : bool)
| If (condition true_branch false_branch : exp)
| Abs (x : var) (e1 : exp)
| App (e1 e2 : exp)

| Loc (l : loc)
(* Like in the last type system for references, explicit locations only appear
 * in the middle of executions.  They shouldn't appear in a program. *)
.

Inductive type :=
| Bool
| Fun (dom ran : type)
.

(* When are two finite maps disjoint? *)
Definition disjoint {K V} (G1 G2 : fmap K V) :=
  forall x t1 t2,
    G1 $? x = Some t1 ->
    G2 $? x = Some t2 ->
    False.

Arguments disjoint / .

(* Finite map [m] splits into disjoint maps [m1] and [m2]. *)
Definition split {K V} (m m1 m2 : fmap K V) :=
  (m1 $<= m) /\
  (m2 $<= m) /\
  disjoint m1 m2 /\
  (forall k, m1 $? k = None -> m2 $? k = None -> m $? k = None).
(* The [$<=] operator is for "submap": all mappings of the first map are also in
 * the second map. *)

(* This is a version of typing rules that doesn't mention explicit locations. It
 * is what we need to type-check a program. *)
Inductive hasty0 : fmap var type -> exp -> type -> Prop :=
| Ht0Var : forall x t,
    hasty0 ($0 $+ (x, t)) (Var x) t
(* Since variable [x] is the whole expression, the context must only contain
 * [x], as we couldn't possibly "use up" any other variables.  A linearly typed
 * expression is obligated to use up all variables in scope! *)

| Ht0Const : forall b,
    hasty0 $0 (Const b) Bool
(* No variable is used, so the context must be empty. *)

| Ht0If : forall G G1 G2 e e1 e2 t,
    hasty0 G1 e Bool ->
    hasty0 G2 e1 t ->
    hasty0 G2 e2 t ->
    split G G1 G2 ->
    hasty0 G (If e e1 e2) t
(* For a compound expression such as [If], we must partition the resource pool
 * (i.e. typing context [G]) and let each subexpression use one subpool. *)

| Ht0Abs : forall G x e1 t1 t2,
    hasty0 (G $+ (x, t1)) e1 t2 ->
    G $? x = None ->
    (* [x] mustn't "shadow" an existing resource, because each resource must be
     * consumed exactly once. *)
    hasty0 G (Abs x e1) (Fun t1 t2)

| Ht0App : forall G G1 G2 e1 e2 t1 t2,
    hasty0 G1 e1 (Fun t1 t2) ->
    hasty0 G2 e2 t1 ->
    split G G1 G2 ->
    hasty0 G (App e1 e2) t2
(* Partitions resource pool, similarly to [If]. *)
.

Hint Constructors hasty0.

Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
  match e2 with
    | Var y => if y ==v x then e1 else Var y
    | Const n => Const n
    | If e2c e2t e2f => If (subst e1 x e2c) (subst e1 x e2t) (subst e1 x e2f)
    | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
    | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
    | Loc l => Loc l
  end.

(* Now let's turn to operational semantics and see how the "consumed once"
 * policy is enforced by the runtime.  To enforce it, we evaluate an expression
 * with a heap.  Every constructed object (e.g. a Boolean value, a function
 * abstraction, etc.) is immediatly put onto the heap, and the expression only
 * retains a pointer.  Once the pointer is used in an elimination step (e.g.
 * condition test, function application, etc.), the object is removed from the
 * heap. Thus, if the expression attempts to use the pointer again, it will get
 * stuck. *)

Definition heap := fmap loc exp.

Inductive value : exp -> Prop :=
| VLoc : forall l, value (Loc l)
(* We only treat pointers as final values, since constructed objects are
 * immediately put onto the heap.  Note that it is especially realistic to
 * represent function values with locations, since real functional-language
 * implementations almost always represent functions with *closures*,
 * dynamically allocated data structures of arbitrary tree shapes, stored in a
 * garbage-collected heap.  The linear type system saves us from needing to do
 * garbage collection, as we can reclaim storage for each value as we use it. *)
.

Inductive step0 : heap * exp -> heap * exp -> Prop :=
| Beta : forall h l x e v,
    h $? l = Some (Abs x e) ->
    value v ->
    step0 (h, App (Loc l) v) (h $- l, subst v x e)
(* Retrieve the function abstraction via the pointer [l] and remove it from the
 * heap. *)

| IfTrue : forall h l e1 e2,
    h $? l = Some (Const true) ->
    step0 (h, If (Loc l) e1 e2) (h $- l, e1)
(* Retrieve the Boolean value via the pointer [l] and remove it from the
 * heap. *)

| IfFalse : forall h l e1 e2,
    h $? l = Some (Const false) ->
    step0 (h, If (Loc l) e1 e2) (h $- l, e2)

| StoreConst : forall h b l,
    h $? l = None ->
    step0 (h, Const b) (h $+ (l, Const b), Loc l)
(* When a value is constructed, it is immediately put onto the heap and referred
 * to by a pointer in the expression. *)

| StoreAbs : forall h x e l,
    h $? l = None ->
    step0 (h, Abs x e) (h $+ (l, Abs x e), Loc l)
.

Inductive context : Set :=
| Hole : context
| If1 : context -> exp -> exp -> context
| App1 : context -> exp -> context
| App2 : exp -> context -> context
.

Inductive plug : context -> exp -> exp -> Prop :=
| PlugHole : forall e, plug Hole e e
| PlugIf1 : forall C e e' e1 e2,
    plug C e e'
    -> plug (If1 C e1 e2) e (If e' e1 e2)
| PlugApp1 : forall e e' C e2,
  plug C e e'
  -> plug (App1 C e2) e (App e' e2)
| PlugApp2 : forall e e' v1 C,
  value v1
  -> plug C e e'
  -> plug (App2 v1 C) e (App v1 e')
.

Inductive step : heap * exp -> heap * exp -> Prop :=
| StepRule : forall C e1 e2 e1' e2' h h',
  plug C e1 e1'
  -> plug C e2 e2'
  -> step0 (h, e1) (h', e2)
  -> step (h, e1') (h', e2').

Definition trsys_of (e : exp) := {|
  Initial := {($0, e)};
  Step := step
|}.


(** * Type soundness *)

(* This is an extended version of the typing rules that involves heap typing.
 * Heap typing is treated in a similar way as the typing context, i.e. it
 * cannot contain unused resources and it is properly partitioned among
 * subexpressions, etc.  *)
Inductive hasty : fmap loc type -> fmap var type -> exp -> type -> Prop :=
| HtVar : forall x t,
    hasty $0 ($0 $+ (x, t)) (Var x) t
(* No mention of locations, so heap typing must be empty. *)

| HtConst : forall b,
    hasty $0 $0 (Const b) Bool

| HtIf : forall H H1 H2 G G1 G2 e e1 e2 t,
    hasty H1 G1 e Bool ->
    hasty H2 G2 e1 t ->
    hasty H2 G2 e2 t ->
    split H H1 H2 ->
    split G G1 G2 ->
    hasty H G (If e e1 e2) t
(* Heap typing [H] is partitioned similarly to typing context [G]. *)

| HtAbs : forall H G x e1 t1 t2,
    hasty H (G $+ (x, t1)) e1 t2 ->
    G $? x = None ->
    hasty H G (Abs x e1) (Fun t1 t2)

| HtApp : forall H H1 H2 G G1 G2 e1 e2 t1 t2,
    hasty H1 G1 e1 (Fun t1 t2) ->
    hasty H2 G2 e2 t1 ->
    split H H1 H2 ->
    split G G1 G2 ->
    hasty H G (App e1 e2) t2

| HtLoc : forall l t,
    hasty ($0 $+ (l, t)) $0 (Loc l) t
(* [l] is the whole expression, so the heap typing contains only [l]. *)
.

Hint Constructors hasty.

(* Some lemmas about [fmap] that are likely to come in handy: *)
Lemma includes_refl K V (m : fmap K V) : m $<= m.
Proof.
  intros.
  eapply includes_intro; intros.
  eauto.
Qed.

Lemma split_0_intro K V (m : fmap K V) : split m $0 m.
Proof.
  intros.
  unfold split in *; simplify; propositional; eauto.
  eapply includes_refl.
Qed.

(* CHALLENGE #1: prove that [hasty0] implies [hasty] with an empty heap. *)

Lemma hasty0_hasty G e t :
  hasty0 G e t ->
  hasty $0 G e t.
Proof.
Admitted.

(* The only things that can be stored on the heap are Boolean constants and
 * function abstractions. *)
Inductive storable : exp -> Prop :=
| SConst : forall b,
    storable (Const b)
| SAbs : forall x e,
    storable (Abs x e)
.

(* The heap is finite. *)
Inductive growable (h : heap) : Prop :=
| Growable : forall bound,
    (forall l, l >= bound -> h $? l = None) ->
    growable h.

Hint Constructors value plug step0 step storable growable.

(* Another bunch of fmap lemmas *)
Lemma fmap_eq_elim {K V} {m1 m2 : fmap K V} : m1 = m2 -> forall k, m1 $? k = m2 $? k.
Proof.
  intros.
  subst.
  eauto.
Qed.

Lemma add_neq_empty K V (m : fmap K V) (k : K) (v : V) : m $+ (k, v) <> $0.
Proof.
  intro H.
  specialize (fmap_eq_elim H k).
  simplify; equality.
Qed.

Lemma includes_elim {K V} {m1 m2 : fmap K V} :
  m1 $<= m2 ->
  forall k v,
    m1 $? k = Some v ->
    m2 $? k = Some v.
Proof.
  intros.
  eauto.
Qed.

Lemma includes_empty K V (m : fmap K V) : m $<= $0 -> m = $0.
Proof.
  intros.
  maps_equal.
  cases (m $? k); eauto.
  specialize (includes_elim H _ _ Heq); simplify; eauto.
Qed.

Lemma split_0 K V (G1 G2 : fmap K V) : split $0 G1 G2 -> G1 = $0 /\ G2 = $0.
Proof.
  intros.
  unfold split in *; propositional; eapply includes_empty; eauto.
Qed.

Ltac t0 := match goal with
           | [ H : ex _ |- _ ] => invert H
           | [ H : _ /\ _ |- _ ] => invert H
           | [ |- context[?x ==v ?y] ] => cases (x ==v y)
           | [ H : Some _ = Some _ |- _ ] => invert H
           | [ H : growable _ |- _ ] => invert H
           | [ H : step _ _ |- _ ] => invert H
           | [ H : step0 _ _ |- _ ] => invert1 H
           | [ H : hasty _ _ ?e _, H' : storable ?e |- _ ] => (invert H'; invert H); []
           | [ H : hasty _ _ ?e _, H' : value ?e |- _ ] => (invert H'; invert H); []
           | [ H : hasty _ _ _ _ |- _ ] => invert1 H
           | [ H : plug _ _ _ |- _ ] => invert1 H
           | [ H : split _ _ _ |- _ ] => eapply split_0 in H
           | [ H : _ $+ (_, _) = $0 |- _ ] => eapply add_neq_empty in H
           | [ H : $0 = _ $+ (_, _) |- _ ] => symmetry in H; eapply add_neq_empty in H
           end; subst.

(* A tactic that will be your friend *)
Ltac t := simplify; propositional; repeat (t0; simplify); try equality; eauto 7.

Hint Extern 2 (exists _ : _ * _, _) => eexists (_ $+ (_, _), _).

(* ========== BEGIN : a WHOLE bunch of [fmap] lemmas! ===================== *)
Lemma includes_None K V (m1 m2 : fmap K V) : m1 $<= m2 -> forall k, m2 $? k = None -> m1 $? k = None.
Proof.
  intros.
  cases (m1 $? k); eauto.
  specialize (includes_elim H _ _ Heq); intros Hsome; t.
Qed.
Hint Resolve includes_None.

Lemma includes_trans K V (m1 m2 m3 : fmap K V) : m1 $<= m2 -> m2 $<= m3 -> m1 $<= m3.
Proof.
  intros.
  eapply includes_intro; intros.
  t.
Qed.

Lemma remove_includes K V (m : fmap K V) k : m $- k $<= m.
Proof.
  intros.
  eapply includes_intro; intros.
  compare_for_equality k0 k.
Qed.

Lemma join_Some_elim K V (m1 m2 : fmap K V) k v : (m1 $++ m2) $? k = Some v -> m1 $? k = Some v \/ m2 $? k = Some v.
Proof.
  intros.
  cases (m1 $? k).
  {
    rewrite lookup_join1 in H; t.
    eapply lookup_Some_dom; eauto.
  }
  {
    rewrite lookup_join2 in H; eauto.
    eapply lookup_None_dom; eauto.
  }
Qed.

Lemma join_None_intro K V (m1 m2 : fmap K V) k : m1 $? k = None -> m2 $? k = None -> (m1 $++ m2) $? k = None.
Proof.
  intros.
  rewrite lookup_join2; eauto.
  eapply lookup_None_dom; eauto.
Qed.

Lemma join_None_elim K V (m1 m2 : fmap K V) k : (m1 $++ m2) $? k = None -> m1 $? k = None /\ m2 $? k = None.
Proof.
  intros.
  cases (m1 $? k).
  {
    rewrite lookup_join1 in H; t.
    eapply lookup_Some_dom; eauto.
  }
  {
    rewrite lookup_join2 in H; eauto.
    eapply lookup_None_dom; eauto.
  }
Qed.

Lemma join_add K V (m1 m2 : fmap K V) k v : m1 $++ m2 $+ (k, v) = m1 $+ (k, v) $++ m2.
Proof.
  intros.
  maps_equal.
  {
    rewrite lookup_join1; simplify; eauto.
    sets.
  }
  cases (m1 $? k0).
  {
    eapply lookup_Some_dom in Heq.
    rewrite lookup_join1; simplify; eauto.
    rewrite lookup_join1; simplify; eauto.
    sets.
  }
  {
    eapply lookup_None_dom in Heq.
    rewrite lookup_join2; simplify; eauto.
    rewrite lookup_join2; simplify; eauto.
    sets.
  }
Qed.

Lemma join_includes K V (m1 m2 m : fmap K V) : m1 $<= m -> m2 $<= m -> m1 $++ m2 $<= m.
Proof.
  intros.
  eapply includes_intro; intros.
  eapply join_Some_elim in H1; t.
Qed.

Lemma includes_join_l K V (m1 m2 : fmap K V) : m1 $<= m1 $++ m2.
Proof.
  eapply includes_intro.
  t.
  rewrite lookup_join1; eauto.
  eapply lookup_Some_dom; eauto.
Qed.

Lemma includes_join_r K V (m1 m2 : fmap K V) : disjoint m1 m2 -> m2 $<= m1 $++ m2.
Proof.
  simplify.
  eapply includes_intro.
  t.
  cases (m1 $? k); subst; simplify.
  {
    exfalso; t.
  }
  rewrite lookup_join2; eauto.
  eapply lookup_None_dom; eauto.
Qed.

Lemma add_remove K V (m : fmap K V) k v : m $? k = None -> m $+ (k, v) $- k = m.
Proof.
  intros.
  maps_equal.
  compare_for_equality k0 k.
Qed.

Lemma add_remove_neq V (m : fmap loc V) k v k' :
  k' <> k ->
  m $+ (k, v) $- k' = m $- k' $+ (k, v).
Proof.
  intros.
  maps_equal.
  cases (k0 ==n k'); subst; simplify; eauto.
Qed.

Lemma remove_add K V (m : fmap K V) k v : m $? k = Some v -> m = m $- k $+ (k, v).
Proof.
  intros.
  maps_equal; eauto.
Qed.

Lemma disjoint_add K V (m1 m2 : fmap K V) k v : disjoint m1 m2 -> m2 $? k = None -> disjoint (m1 $+ (k, v)) m2.
Proof.
  t.
Qed.

Lemma split_symm {K V} {m m1 m2 : fmap K V} : split m m1 m2 -> split m m2 m1.
Proof.
  intros.
  unfold split in *; t.
Qed.

Lemma join_split K V (m1 m2 : fmap K V) : disjoint m1 m2 -> split (m1 $++ m2) m1 m2.
Proof.
  intros.
  unfold split in *; t.
  {
    eapply includes_join_l; eauto.
  }
  {
    eapply includes_join_r; eauto.
  }
  {
    eapply join_None_intro; eauto.
  }
Qed.

Lemma split_to_0 K V (m m2 : fmap K V) : split m $0 m2 -> m = m2.
Proof.
  intros.
  unfold split in *; t.
  maps_equal.
  cases (m2 $? k); t.
Qed.

Lemma split_0_intro_r K V (m : fmap K V) : split m m $0.
Proof.
  eapply split_symm.
  eapply split_0_intro.
Qed.

Lemma split_singleton_elim K V (m m2 : fmap K V) k v : split m ($0 $+ (k, v)) m2 -> m = m2 $+ (k, v) /\ m2 $? k = None.
Proof.
  unfold split in *.
  t.
  {
    maps_equal.
    eapply includes_lookup; eauto; simplify; eauto.
    cases (m2 $? k0).
    {
      eapply includes_lookup; eauto; simplify; eauto.
    }
    eapply H3; simplify; eauto.
  }
  {
    cases (m2 $? k); try trivial.
    exfalso.
    eapply H1; eauto.
    simplify; eauto.
  }
Qed.

Lemma split_lookup_same K V (m m1 m2 : fmap K V) k v1 v2 : split m m1 m2 -> m $? k = Some v1 -> m1 $? k = Some v2 -> v2 = v1.
Proof.
  intros.
  assert (Hinc : m1 $<= m) by (unfold split in *; t).
  specialize (includes_elim Hinc _ _ H1); intros Hsome.
  rewrite H0 in Hsome.
  equality.
Qed.

Lemma split_None K V (m m1 m2 : fmap K V) k : split m m1 m2 -> m $? k = None -> m1 $? k = None /\ m2 $? k = None.
Proof.
  intros.
  unfold split in *; t.
Qed.

Lemma split_remove K V (m m1 m2 : fmap K V) k v : split m m1 m2 -> m1 $? k = Some v -> split (m $- k) (m1 $- k) m2.
Proof.
  intros.
  unfold split in *; t.
  {
    eapply includes_intro; intros.
    compare_for_equality k0 k;
      specialize (includes_elim H1 _ _ H3); intros Hv; simplify; t.
  }
  {
    eapply includes_intro; intros.
    compare_for_equality k0 k;
      specialize (includes_elim H _ _ H3); intros Hv; simplify; t.
    exfalso; t.
  }
  {
    compare_for_equality x k;
      specialize (includes_elim H _ _ H5); intros Hv; simplify; t.
  }
  {
    compare_for_equality k0 k;
    t.
  }
Qed.

Lemma split_distr_intro K V (G G1 G2 : fmap K V) k v :
  split G G1 G2 ->
  G $? k = None ->
  split (G $+ (k, v)) (G1 $+ (k, v)) G2.
Proof.
  intros.
  unfold split in *; t.
  {
    eapply includes_intro; intros.
    compare_for_equality k0 k;
      specialize (includes_elim H _ _ H3); intros Hv; simplify; t.
  }
  {
    compare_for_equality x k;
      specialize (includes_elim H _ _ H5); intros Hv; simplify; t.
  }
  {
    compare_for_equality k0 k;
    t.
  }
Qed.

Lemma split_distr K V (G G1 G2 : fmap K V) k v :
  split (G $+ (k, v)) G1 G2 ->
  G $? k = None ->
  G1 = G1 $- k $+ (k, v) /\ G2 $? k = None /\ split G (G1 $- k) G2 \/
                                            G2 = G2 $- k $+ (k, v) /\ G1 $? k = None /\ split G G1 (G2 $- k).
Proof.
  intros.
  unfold split in *.
  cases (G1 $? k); subst; simplify.
  {
    left.
    assert (Hv : v0 = v).
    {
      t.
      specialize (includes_elim H1 _ _ Heq); intros Hv; simplify.
      t.
    }
    subst.
    t; eauto.
    {
      eapply remove_add; eauto.
    }
    {
      cases (G2 $? k); eauto.
      exfalso; t.
    }
    {
      eapply includes_intro; intros.
      compare_for_equality k0 k;
      specialize (includes_elim H1 _ _ H3); intros Hv; simplify.
      eauto.
    }
    {
      cases (G2 $? k); eauto.
      {
        exfalso; t.
      }
      eapply includes_intro; intros.
      compare_for_equality k0 k;
      specialize (includes_elim H _ _ H3); intros Hv; simplify.
      eauto.
    }
    {
      compare_for_equality x k;
      exfalso; t.
    }
    {
      compare_for_equality k0 k;
      specialize (H4 k0); t.
    }
  }
  cases (G2 $? k); subst; simplify.
  {
    right.
    assert (Hv : v0 = v).
    {
      t.
      specialize (includes_elim H _ _ Heq0); intros Hv; simplify.
      t.
    }
    subst.
    t; eauto.
    {
      eapply remove_add; eauto.
    }
    {
      eapply includes_intro; intros.
      compare_for_equality k0 k;
      specialize (includes_elim H1 _ _ H3); intros Hv; simplify.
      eauto.
    }
    {
      eapply includes_intro; intros.
      compare_for_equality k0 k;
      specialize (includes_elim H _ _ H3); intros Hv; simplify.
      eauto.
    }
    {
      compare_for_equality x k;
      exfalso; t.
    }
    {
      compare_for_equality k0 k;
      specialize (H4 k0); t.
    }
  }
  t.
  specialize (H4 k); t.
Qed.

Lemma split_singleton_intro K V (m : fmap K V) k v : m $? k = None -> split (m $+ (k, v)) ($0 $+ (k, v)) m.
Proof.
  intros.
  eapply split_distr_intro; eauto.
  eapply split_0_intro.
Qed.

Lemma split_twice {K V} {m m1 m2 m1a m1b : fmap K V} : split m m1 m2 -> split m1 m1a m1b -> split m (m1a $++ m2) m1b /\ split (m1a $++ m2) m1a m2.
Proof.
  intros.
  unfold split in *.
  t; eauto using includes_trans.
  {
    eapply join_includes; eauto using includes_trans.
  }
  {
    eapply join_Some_elim in H5.
    t.
  }      
  {
    eapply join_None_elim in H5.
    t.
  }
  {
    eapply includes_join_l; eauto.
  }
  {
    eapply includes_join_r; t.
  }
  {
    eapply join_None_intro; eauto.
  }
Qed.
(* ========== END : a WHOLE bunch of [fmap] lemmas! ===================== *)

(* some [growable] lemmas *)
Lemma growable_0 : growable $0.
Proof.
  eapply Growable with (bound := 0).
  simplify.
  eauto.
Qed.

Lemma growable_singleton m k v : growable m -> growable (m $+ (k, v)).
Proof.
  intros.
  invert H.
  eapply Growable with (bound := max bound (k + 1)).
  intros.
  cases (l ==n k); subst; simplify; try linear_arithmetic.
  eapply H0; linear_arithmetic.
Qed.

(* We need a relation describing when a heap adheres to a heap typing.  Getting
 * it right turned out to be very tricky!  So we'll just give it away here, with
 * all the lemmas about it that you'll need. *)
Inductive heapty : fmap loc type -> heap -> Prop :=
| HtEmpty :
    heapty $0 $0
| HtAdd : forall ht h l t e ht'' ht',
    ht $? l = None ->
    h $? l = None ->
    storable e ->
    split ht'' ht ht' ->
    (* Heap cells in [h $+ (l, e)] reachable from [e] are accounted as [e]'s private 
       resources, so they are not covered by [ht]. However, when we remove [(l, e)] 
       from [h $+ (l, e)], those cells are exposed and no longer [e]'s private 
       resources, so there must exists some extra heap typing [ht'] to cover them. *)
    heapty ht'' h ->
    (* [h] is therefore covered by [ht $++ ht'], which is [ht'']. *)
    hasty ht' $0 e t ->
    (* the extra heap typing [ht'] should actually cover [e]'s private resources *)
    heapty (ht $+ (l, t)) (h $+ (l, e))
.

Hint Constructors heapty.

Lemma heapty_elim_None ht h :
  heapty ht h ->
  forall l,
    h $? l = None ->
    ht $? l = None.
Proof.
  induct 1; t.
  cases (l0 ==n l); subst; simplify; try equality.
  eapply IHheapty in H5.
  eapply split_None in H2; t.
Qed.

Lemma split_heapty ht h :
  heapty ht h ->
  forall ht1 ht2,
    split ht ht1 ht2 ->
    exists h1 h2,
      split h h1 h2 /\
      heapty ht1 h1 /\
      heapty ht2 h2.
Proof.
  induct 1; t.
  {
    exists $0, $0.
    t.
    eapply split_0_intro; eauto.
  }
  generalize H5; intro Hsp.
  eapply split_distr in Hsp; try trivial.
  t.
  {
    assert (Hsp : split ht'' (ht1 $- l $++ ht') ht2).
    {
      specialize (split_twice H2 H9); intros Hsp.
      t.
    }
    eapply IHheapty in Hsp.
    destruct Hsp as [h1 [h2 Hsp] ].
    propositional.
    assert (Hsp : split (h $+ (l, e)) (h1 $+ (l, e)) h2).
    {
      eapply split_distr_intro; eauto.
    }
    do 2 eexists; t.
    rewrite H7.
    assert (Hsp2 : split (ht1 $- l $++ ht') (ht1 $- l) ht').
    {
      specialize (split_twice H2 H9); intros Hsp3.
      t.
    }
    econstructor; simplify; try trivial.
    {
      eapply split_None in H8; eauto.
      propositional.
    }
    {
      eapply Hsp2.
    }
    {
      eauto.
    }
    {
      eauto.
    }
  }
  {
    assert (Hsp : split ht'' ht1 (ht2 $- l $++ ht')).
    {
      specialize (split_twice H2 (split_symm H9)); intros Hsp.
      t.
      eapply split_symm; eauto.
    }
    eapply IHheapty in Hsp.
    destruct Hsp as [h1 [h2 Hsp] ].
    propositional.
    assert (Hsp : split (h $+ (l, e)) h1 (h2 $+ (l, e))).
    {
      eapply split_symm.
      eapply split_distr_intro; eauto.
      eapply split_symm; eauto.
    }
    do 2 eexists; t.
    rewrite H7.
    assert (Hsp2 : split (ht2 $- l $++ ht') (ht2 $- l) ht').
    {
      specialize (split_twice H2 (split_symm H9)); intros Hsp3.
      t.
    }
    econstructor; simplify; try trivial.
    {
      eapply split_None in H8; eauto.
      propositional.
    }
    {
      eapply Hsp2.
    }
    {
      eauto.
    }
    {
      eauto.
    }
  }
Qed.

Lemma split_heapty_intro h1 ht1 : 
  heapty ht1 h1 ->
  forall h ht2 h2,
    split h h1 h2 ->
    heapty ht2 h2 ->
    exists ht,
      split ht ht1 ht2 /\
      heapty ht h.
Proof.
  induct 1; t.
  {
    eapply split_to_0 in H.
    subst.
    exists ht2.
    propositional.
    eapply split_0_intro.
  }
  assert (Hsp : split (h0 $- l) h h2).
  {
    eapply split_remove with (k := l) in H5; simplify; eauto.
    rewrite add_remove in H5 by (simplify; eauto).
    eauto.
  }
  assert (Hh0 : h0 = h0 $- l $+ (l, e)).
  {
    eapply remove_add.
    unfold split in *; t.
    specialize (includes_elim H2 l); simplify; eauto.
  }
  eapply IHheapty in Hsp; eauto.
  destruct Hsp as [Ht''' Hsp].
  propositional.
  exists (ht $++ ht2 $+ (l, t)).
  assert (Hsp : split Ht''' (ht $++ ht2) ht').
  {
    specialize (split_twice H7 H2); intros Hsp.
    t.
  }
  assert (Hsp2 : split (ht $++ ht2) ht ht2).
  {
    specialize (split_twice H7 H2); intros Hsp2.
    t.
  }
  assert (Hnone : (ht $++ ht2) $? l = None).
  {
    eapply heapty_elim_None with (l := l) in H8; simplify; eauto.
    eapply split_None in Hsp; t.
  }
  propositional.
  {
    rewrite join_add.
    eapply join_split.
    eapply disjoint_add.
    {
      unfold split in *; t.
    }
    eapply split_None in Hnone; t.
  }
  rewrite Hh0.
  econstructor; simplify; try trivial.
  {
    eapply Hsp.
  }
  {
    eauto.
  }
  {
    eauto.
  }
Qed.

Lemma heapty_elim ht h :
  heapty ht h ->
  (forall l t,
      ht $? l = Some t ->
      exists e ht' ht'',
        h $? l = Some e /\
        storable e /\
        split ht'' (ht $- l) ht' /\            
        heapty ht'' (h $- l) /\
        hasty ht' $0 e t) /\
  (ht = $0 -> h = $0).
Proof.
  induct 1; t.
  cases (l0 ==n l); subst; simplify.
  {
    invert H7.
    repeat rewrite add_remove by (simplify; eauto).
    do 3 eexists; t.
  }
  assert (Hht'' : ht'' $? l0 = Some t0) by (unfold split in *; t).
  repeat rewrite add_remove_neq by eauto.
  eapply H5 in Hht''.
  t.
  exists x, x0, (ht $- l0 $++ x0 $+ (l, t)).
  assert (Hsp0 : split (ht'' $- l0) (ht $- l0) ht').
  {
    eapply split_remove in H2; eauto.
  }
  assert (Hsp : split x1 (ht $- l0 $++ x0) ht').
  {
    specialize (split_twice H10 Hsp0); intros Hsp.
    t.
  }
  assert (Hsp2 : split (ht $- l0 $++ x0) (ht $- l0) x0).
  {
    specialize (split_twice H10 Hsp0); intros Hsp2.
    t.
  }
  assert (Hnone : (ht $- l0 $++ x0) $? l = None).
  {
    eapply heapty_elim_None with (l := l) in H11; t.
    eapply split_None in Hsp; t.
  }
  t; try trivial.
  {
    rewrite join_add.
    eapply join_split.
    eapply disjoint_add.
    {
      unfold split in *; t.
    }
    eapply split_None in Hnone; t.
  }
  econstructor; simplify; try trivial.
  {
    eapply Hsp.
  }
  {
    eauto.
  }
  {
    eauto.
  }
Qed.

(* The next challenge is to prove the safety of well-typed programs.  We break
 * it apart into several challenges to make it more manageable. *)

(* CHALLENGE #2: prove this [progress'] lemma. *)
Lemma progress' : forall ht e t,
    hasty ht $0 e t ->
    forall h h',
      heapty ht h ->
      h $<= h' ->
      growable h' ->
      value e
      \/ exists he', step (h', e) he'.
Proof.
Admitted.

Hint Resolve includes_refl.
Hint Resolve remove_includes.
Hint Resolve split_0_intro.
Hint Resolve split_0_intro_r.
Hint Resolve split_singleton_intro.
Hint Resolve split_remove.
Hint Resolve split_distr_intro.
Hint Resolve growable_singleton.
Hint Resolve growable_0.

Lemma progress : forall ht e t h,
    hasty ht $0 e t ->
    heapty ht h ->
    growable h ->
    value e
    \/ exists he', step (h, e) he'.
Proof.
  t.
  eapply progress' with (h := h) (h' := h) in H; eauto.
Qed.

Lemma weakening_override : forall (G G' : fmap var type) x t,
  (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
  -> (forall x' t', G $+ (x, t) $? x' = Some t'
                    -> G' $+ (x, t) $? x' = Some t').
Proof.
  simplify.
  cases (x ==v x'); simplify; eauto.
Qed.

Hint Resolve weakening_override.

Lemma hasty_change : forall H G e t,
  hasty H G e t
  -> forall G', G' = G
    -> hasty H G' e t.
Proof.
  t.
Qed.

Hint Resolve hasty_change.

(* A property about extending heap typings *)
Lemma heap_override : forall H h k t t0 l,
  H $? k = Some t
  -> heapty H h
  -> h $? l = None
  -> H $+ (l, t0) $? k = Some t.
Proof.
  intros.
  eapply heapty_elim in H1.
  t.
  cases (l ==n k); subst; simplify; eauto.
  apply H3 in H0; t.
Qed.

Hint Resolve heap_override.

(* CHALLENGE #3: prove this [preservation0] lemma. *)
Lemma preservation0 : forall h1' e1 h2' e2,
    step0 (h1', e1) (h2', e2) ->
    forall h1 hctx H1 t,
      split h1' h1 hctx ->
      heapty H1 h1 ->
      growable h1' ->
      hasty H1 $0 e1 t ->
      exists H2 h2,
        hasty H2 $0 e2 t /\
        heapty H2 h2 /\
        growable h2' /\
        split h2' h2 hctx.
Proof.
Admitted.

Hint Resolve preservation0.

(* CHALLENGE #4: prove this [generalize_plug] lemma. *)
Lemma generalize_plug : forall C e1 e1',
  plug C e1 e1' ->
  forall H t,
    hasty H $0 e1' t ->
    exists H1 Hctx t0,
      hasty H1 $0 e1 t0 /\
      split H H1 Hctx /\
      forall e2 e2' H1' H',
        hasty H1' $0 e2 t0 ->
        plug C e2 e2' ->
        split H' H1' Hctx ->
        hasty H' $0 e2' t.
Proof.
Admitted.

(* CHALLENGE #5: prove [preservation]. *)
Lemma preservation : forall h1 e1 h2 e2,
  step (h1, e1) (h2, e2) ->
  forall H1 t,
    hasty H1 $0 e1 t ->
    heapty H1 h1 ->
    growable h1 ->
    exists H2,
      hasty H2 $0 e2 t /\
      heapty H2 h2 /\
      growable h2.
Proof.
Admitted.

Hint Resolve progress preservation.

(* CHALLENGE #6: prove theorem [safety]. *)
Theorem safety : forall e t, hasty $0 $0 e t
  -> invariantFor (trsys_of e)
                  (fun he' => value (snd he')
                              \/ exists he'', step he' he'').
Proof.
Admitted.
