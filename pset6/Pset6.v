Require Import Frap Pset6Sig.

Set Implicit Arguments.

(** * Universal polymorphism *)

(* Raising a typing derivation to a larger typing context *)
Lemma weakening : forall L G e t,
    hasty L G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
                  -> hasty L G' e t.
Proof.
Admitted.

Hint Resolve weakening.

(** The counterpart of [weakening] for [wfty] *)
Lemma weakening_wfty : forall L t,
    wfty L t
    -> forall L', (forall x t, L $? x = Some t -> L' $? x = Some t)
                  -> wfty L' t.
Proof.
Admitted.

Hint Resolve weakening_wfty.

(* The counterpart of [weakening] for type variables *)
Lemma weakening_t : forall L G e t,
    hasty L G e t
    -> forall L', (forall x t, L $? x = Some t -> L' $? x = Some t)
                  -> hasty L' G e t.
Proof.
Admitted.

Hint Resolve weakening_t.

(* Replacing a variable with a properly typed term preserves typing. *)
Lemma substitution : forall L G x t' e t e',
    hasty L (G $+ (x, t')) e t
    -> hasty $0 $0 e' t'
    -> hasty L G (subst e' x e) t.
Proof.
Admitted.

Hint Resolve substitution.

(* Replacing a type variable with a well-formed type preserves
 * wellformedness. *)
Lemma substitution_t_t : forall L x t t',
    wfty (L $+ (x, tt)) t
    -> wfty $0 t'
    -> wfty L (subst_t_t t' x t).
Proof.
Admitted.

Hint Resolve substitution_t_t.

(* Replacing a type variable with a well-formed type preserves typing. *)
Lemma substitution_t_e : forall L G x e t t',
    hasty (L $+ (x, tt)) G e t
    -> wfty $0 t'
    (* G' includes [fmap_map (subst_t_t t' x) G], where [fmap_map f m] means
     * apply [f] to every value of [m].  [fmap_map] is not defined in [Frap],
     * so we use this Prop-y version. *)
    -> forall G',
        (forall y t, G $? y = Some t -> G' $? y = Some (subst_t_t t' x t))
        -> hasty L G' (subst_t_e t' x e) (subst_t_t t' x t).
Proof.
Admitted.

Hint Resolve substitution_t_e.

Theorem safety : forall e t, hasty $0 $0 e t
                             -> invariantFor (trsys_of e)
                                             (fun e' => value e'
                                                        \/ exists e'', step e' e'').
Proof.
Admitted.
