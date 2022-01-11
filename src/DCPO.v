
Set Universe Polymorphism.

Class partial_order := {
    carrier : Type;
    rel  : carrier -> carrier -> Prop; 
    refl : forall x, rel x x;
    asym : forall x y, rel x y -> rel y x -> x = y;
    tran : forall x y z, rel x y -> rel y z -> rel x z;
}.

Notation "[ D ]" := (@carrier D) (at level 9).
Notation "a ≤ b" := (@rel _ a b) (at level 40, left associativity).
 
Definition is_directed {D : partial_order} (Δ : [D] -> Prop) := 
    exists x, Δ x /\ forall x y, exists z, Δ x -> Δ y -> Δ z -> (x ≤ z) -> y ≤ z.

Lemma is_directed_r {D : partial_order} {Δ : [D] -> Prop} (h : is_directed Δ) : 
    forall x y, exists z, Δ x -> Δ y -> Δ z -> (x ≤ z) -> y ≤ z.
Proof.
now elim h.
Qed.

Definition is_upper_bound_ {D : partial_order} (Δ : [D] -> Prop) (x : [D]) :=
    forall y, Δ y -> y ≤ x.

Definition is_least_upper_bound {D : partial_order} (Δ : [D] -> Prop) (x : [D]) :=
    forall y, is_upper_bound_ Δ x -> is_upper_bound_ Δ y -> x ≤ y.

Definition has_least_upper_bound {D : partial_order} (Δ : [D] -> Prop) := 
    exists x0, is_least_upper_bound Δ x0. 

Class LUB {D : partial_order} (Δ : [D] -> Prop) := {
    least_upper_bound : [D];
    is_upper_bound : is_upper_bound_ Δ least_upper_bound;
}.

Class DCPO := {
    DCPO_po :> partial_order;
    complete_directed : forall Δ, is_directed Δ -> LUB Δ;
}.

Coercion DCPO_po : DCPO >-> partial_order.

Notation "⋁ Δ hDir" := (@least_upper_bound _ Δ (complete_directed Δ hDir)) (at level 9).

Definition is_continuous {D E : DCPO} (f : D -> E) := 
    forall Δ, is_directed Δ -> f.




