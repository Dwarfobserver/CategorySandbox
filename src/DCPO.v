Require Import Tactics ProofIrrelevance.
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
    (exists x, Δ x) /\ forall x y, Δ x -> Δ y -> exists z, Δ z /\ x ≤ z /\ y ≤ z.

Lemma is_directed_r {D : partial_order} {Δ : [D] -> Prop} (h : is_directed Δ) : 
    forall x y, Δ x -> Δ y -> exists z, Δ z /\ x ≤ z /\ y ≤ z.
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
    cp_dir : forall Δ, is_directed Δ -> LUB Δ;
}.

Coercion DCPO_po : DCPO >-> partial_order.
Definition subset (D : DCPO) := [D] -> Prop .

Notation "⋁ Δ" := (@least_upper_bound _ Δ _) (at level 9).

Definition set_app {A B : Type} (f : A -> B) (X : A -> Prop) : B -> Prop := 
    fun b => exists a, X a /\ b = f a.

Notation "f | X" := (@set_app _ _ f X) (at level 9).

Definition monotonic {D E : DCPO} (f : [D] -> [E]) := forall x y, x ≤ y -> f x ≤ f y.

Lemma monotonic_preserves_directed {D E : DCPO} (f : [D] -> [E]) (h : monotonic f) (Δ : subset D) :
    is_directed Δ -> is_directed f|Δ.
Proof.
intros. destruct H as ((d, d_belong), Hdirected). split. exists (f d). exists d. now split.
intros. destruct H as (x0, (x0_h1, x0_h2)), H0 as (y0, (y0_h1, y0_h2)).
destruct (Hdirected x0 y0 x0_h1 y0_h1) as (z0, z0_h).
exists (f z0). intros. split. exists z0. tauto.
rewrite x0_h2, y0_h2. split; apply h; tauto.
Qed. 


Definition preserve_lub_ {D E : DCPO} (f : [D] -> [E]) (Δ : subset D) (lub_Δ : LUB Δ) (lub_fΔ : LUB f|Δ) := 
    f ⋁Δ = ⋁ (f|Δ).

Definition lub_pass_trough {D E : DCPO} (f : [D] -> [E]) (h : monotonic f) (Δ : subset D) (hD : is_directed Δ) := 
    (cp_dir f|Δ (monotonic_preserves_directed f h Δ hD)).

Class is_continuous {D E : DCPO} (f : [D] -> [E]) := {
    h_mono : monotonic f;
    preserve_lub : forall (Δ : subset D) (hD : is_directed Δ),  preserve_lub_ f Δ (cp_dir Δ hD) (lub_pass_trough f h_mono Δ hD)
}. 
Notation "f ↑" := (@h_mono _ _ f _) (at level 6).

Lemma compose_monotonic {D E F: DCPO} (f : [D] -> [E]) (g : [E] -> [F]) (hf : is_continuous f) (hg : is_continuous g) : 
    monotonic (fun x => g (f x)).
Proof.
unfold monotonic. intros. now apply g↑, f↑.
Qed.

Program Definition continuous_compose {D E F: DCPO} (f : [D] -> [E]) (g : [E] -> [F]) (hf : is_continuous f) (hg : is_continuous g) : 
    is_continuous (fun x => g (f x)) := {|
        h_mono := compose_monotonic f g hf hg;
    |}.
Next Obligation.
unfold preserve_lub_. 
pose (lub_Δ := cp_dir Δ hD).
pose (lub_fΔ := lub_pass_trough f f↑ Δ hD).
assert (f ⋁Δ = ⋁ (f|Δ)). apply preserve_lub.
unfold least_upper_bound.
unfold least_upper_bound, lub_Δ in H.
rewrite H.

