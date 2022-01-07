(* Not useful anymore because Cone now comes from Comma *)
(* Require Import Category Functor Transform Limit.
Require Import FunctionalExtensionality ProofIrrelevance.

Class cone {I C : Category} (D : I → C) := {
    base : [C];
    tf : Δ[base] ⇒ D;
}.

Notation "base[ d ]" := (@base _ _ _ d) (at level 9).
Notation "tf[ d ]" := (@tf _ _ _ d) (at level 9).


Class cone_hom {I C : Category} {D : I → C} (δ δ' : cone D) := {
    mph : base[δ] ~> base[δ'];
    commute : forall i : [I], mph >> tf[δ'] i = tf[δ] i; 
}.

Notation "mph[ d , d' ]" := (@mph _ _ _ d d') (at level 9).
Notation "commute[ d , d' ]" := (@commute _ _ _ d d') (at level 9).

Program Definition id_cone_mph {I C : Category} {D : I → C} (δ : cone D) : cone_hom δ δ := {|
    mph := id (base[δ]);
|}.
Next Obligation.
now rewrite cat_id_l.
Defined.

Program Definition comp_cone_mph {I C : Category} {D : I → C} 
    (δ δ' δ'' : cone D) (s : cone_hom δ δ') (t : cone_hom δ' δ'') := {|
    mph := mph[δ, δ'] >> mph[δ', δ''];
|}.
Next Obligation.
now rewrite cat_comp_assoc, (commute[δ', δ''] i), (commute[δ, δ'] i).
Defined.

Program Definition cone_cat {I C : Category} {D : I → C} : Category := {|
    ob := cone D;
    hom := cone_hom;

    id := id_cone_mph;
    comp := comp_cone_mph;
|}.
Next Obligation.
unfold comp_cone_mph.

Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Notation "Δ[ D ]" := (@cone_cat _ _ D) (at level 9).

Definition is_limit {I C : Category} {D : I → C} (δ : [Δ[D]]) := @is_terminal Δ[D] δ.

Lemma limits_are_isom {I C : Category} (D : I → C) (δ δ' : [Δ[D]]) :
    is_limit δ -> is_limit δ' -> δ ≃ δ'.
Proof.
apply terminals_are_isom.
Qed.

*)



