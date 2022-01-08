Require Import Category Functor Transform Comma Limit.
Require Import Equality ProofIrrelevance.


Module Pullback. 
(*
    Pullback diagram : 
    X ---> Z < --- Y
*)
Inductive Obj := X | Y | Z.


Definition Hom (x y : Obj) : Prop := 
    match x, y with
    | X, X => True
    | Y, Y => True
    | Z, Z => True
    | X, Z => True
    | Y, Z => True
    | _, _ => False
    end.

Definition Id (x : Obj) : Hom x x.
destruct x; now simpl.
Qed.

Program Definition Cat : Category := {|
    ob := Obj;
    hom := Hom;
    id  := Id;
|}.
Next Obligation.
destruct a, b, c; now simpl.
Qed.
Next Obligation.
apply proof_irrelevance.
Qed.
Next Obligation.
apply proof_irrelevance.
Qed.
Next Obligation.
apply proof_irrelevance.
Qed.

Definition X_to_Z : @hom Cat X Z := I.
Definition Y_to_Z : @hom Cat Y Z := I.

Definition diagram_ob {C : Category} (a b c : [C]) (x : Obj) : [C] := 
    match x with
    | X => a
    | Y => b
    | Z => c
    end.

(* Any idea to simplify ?*)
Definition diagram_hom {C : Category} {a b c : [C]} (f : a ~> c) (g : b ~> c) (x y : Obj) (t : Hom x y) : 
    diagram_ob a b c x ~> diagram_ob a b c y := 
    match x, y, t with
    | X, Z, _ => f
    | Y, Z, _ => g 
    | X, X, _ => id a
    | Y, Y, _ => id b 
    | Z, Z, _ => id c
    | _, _, t => match t with end
    end.


Program Definition construct_diagram {C : Category} {a b c : [C]} (f : a ~> c) (g : b ~> c) : Cat → C := {|
    f_ob := diagram_ob a b c;
    f_hom := diagram_hom f g
|}.
Next Obligation.
destruct a0; now simpl.
Defined.
Next Obligation.
destruct a0, b0, c0; simpl; try rewrite cat_id_l; try rewrite cat_id_r; now simpl.
Defined.


End Pullback.

Definition is_pullback {C : Category} {D : Pullback.Cat → C} (p : [cone_cat D]) := is_limit p.

Definition pullback_obj {C : Category} {D : Pullback.Cat → C} (p : [cone_cat D]) : [C] := cone_base p.

Definition pullback_to_a_mph {C : Category} {D : Pullback.Cat → C} (p : [cone_cat D]) : pullback_obj p ~> ob[D] Pullback.X := 
    tf[cone_transform p] Pullback.X. 

Definition pullback_to_b_mph {C : Category} {D : Pullback.Cat → C} (p : [cone_cat D]) : pullback_obj p ~> ob[D] Pullback.Y := 
    tf[cone_transform p] Pullback.Y.

Lemma pullback_square_commute {C : Category} {D : Pullback.Cat → C} (p : [cone_cat D]) :
    pullback_to_a_mph p >> hom[D] Pullback.X_to_Z = pullback_to_b_mph p >> hom[D] Pullback.Y_to_Z.
Proof.
assert (pullback_to_a_mph p >> hom[D] Pullback.X_to_Z = tf[cone_transform p] Pullback.Z).
- now rewrite <- (cone_naturality p Pullback.X_to_Z).
- rewrite H. now rewrite <- (cone_naturality p Pullback.Y_to_Z).
Qed.

Definition tf_pullback {C : Category} {D : Pullback.Cat → C} (x : [C]) (f : x ~> ob[D] Pullback.X) (g : x ~> ob[D] Pullback.Y) :=  
    fun i : [Pullback.Cat] =>    
        match i with
        | Pullback.X => f
        | Pullback.Y => g
        | Pullback.Z => f >> hom[D] Pullback.X_to_Z
        end.

(* We prove that if we have a commutative square, we have what we need to construct a cone *)
Lemma nat_pullback {C : Category} {D : Pullback.Cat → C} (x : [C]) (f : x ~> ob[D] Pullback.X) (g : x ~> ob[D] Pullback.Y) 
(square_commute : f >> hom[D] Pullback.X_to_Z = g >> hom[D] Pullback.Y_to_Z) :  
    (forall i j : [Pullback.Cat], forall u : i ~> j, tf_pullback x f g i >> hom[D] u = tf_pullback x f g j).
Proof.
intros. destruct i, j; simpl.
- assert (I = @id Pullback.Cat Pullback.X). apply proof_irrelevance. assert (hom[D] u = id _). 
destruct u. rewrite <- f_id_distr. now rewrite H. now rewrite H0, cat_id_r.
- destruct u.
- destruct u. now unfold Pullback.X_to_Z.
- destruct u.
- assert (I = @id Pullback.Cat Pullback.Y). apply proof_irrelevance. assert (hom[D] u = id _).
destruct u. rewrite <- f_id_distr. now rewrite H. now rewrite H0, cat_id_r.  
- rewrite square_commute. destruct u. now unfold Pullback.Y_to_Z.
- destruct u.
- destruct u.
- assert (I = @id Pullback.Cat Pullback.Z). apply proof_irrelevance. assert (hom[D] u = id _).
destruct u. now rewrite <- f_id_distr, H. now rewrite H0, cat_id_r.
Qed.

(* And now, we construct such a cone *)
Definition commutative_pullback_square_to_cone {C : Category} (D : Pullback.Cat → C) (x : [C]) (f : x ~> ob[D] Pullback.X) (g : x ~> ob[D] Pullback.Y) 
    (square_commute : f >> hom[D] Pullback.X_to_Z = g >> hom[D] Pullback.Y_to_Z) : [cone_cat D].
Proof.
exact (@construct_cone Pullback.Cat C D x (tf_pullback x f g) (nat_pullback x f g square_commute)).
Defined.


(* Now, when we have to pullback cones and a morphism between the two such that the upper and lwoer triangles commute,
we can create a morphism of cone thanks to this definition *)
(* First a lemma that ensures the naturality of the cone morphism we'll construct between cones *)
Lemma naturality_pullback_morphism {C : Category} {D : Pullback.Cat → C} (p1 p2 : [cone_cat D]) (mph : cone_base p1 ~> cone_base p2)
    (lower_nat : mph >> pullback_to_a_mph p2 = pullback_to_a_mph p1) (upper_nat : mph >> pullback_to_b_mph p2 = pullback_to_b_mph p1) :
    forall i : [Pullback.Cat], tf[cone_transform p1] i = mph >> tf[cone_transform p2] i.
Proof.
intro. destruct i; unfold pullback_to_a_mph, pullback_to_b_mph in *; apply eq_sym; try assumption.
now rewrite <- (cone_naturality p2 Pullback.X_to_Z), <- cat_comp_assoc, lower_nat, <- (cone_naturality p1 Pullback.X_to_Z).
Qed.

Definition pullback_morphism_to_cone_morphism {C : Category} (D : Pullback.Cat → C) (p1 p2 : [cone_cat D]) (mph : cone_base p1 ~> cone_base p2)
    (lower_nat : mph >> pullback_to_a_mph p2 = pullback_to_a_mph p1) (upper_nat : mph >> pullback_to_b_mph p2 = pullback_to_b_mph p1) :
    p1 ~> p2 := morphism_to_cone_morphism p1 p2 mph (naturality_pullback_morphism p1 p2 mph lower_nat upper_nat).

Lemma pullback_preserves_mono_b {C : Category} {D : Pullback.Cat → C} (p : [cone_cat D]) (hyp_pullback : is_pullback p) :
    is_mono (hom[D] Pullback.Y_to_Z) -> is_mono (pullback_to_a_mph p).
Proof.
intros. unfold is_mono. intros.
assert (g >> pullback_to_a_mph p >> (hom[D] Pullback.X_to_Z) = g' >> pullback_to_a_mph p >> (hom[D] Pullback.X_to_Z)).
now rewrite H0.
rewrite !cat_comp_assoc in H1.
rewrite (pullback_square_commute p) in H1.
assert (g >> pullback_to_b_mph p = g' >> pullback_to_b_mph p).
- rewrite <- !cat_comp_assoc in H1. unfold is_mono in H. now specialize (H x (g >> pullback_to_b_mph p) (g' >> pullback_to_b_mph p) H1).
- assert (g >> pullback_to_b_mph p >> hom[D] Pullback.Y_to_Z = g >> pullback_to_a_mph p >> hom[D] Pullback.X_to_Z).
now rewrite !cat_comp_assoc, pullback_square_commute.
apply eq_sym in H3. 
assert (g' >> pullback_to_a_mph p >> hom[D] Pullback.X_to_Z = g' >> pullback_to_b_mph p >> hom[D] Pullback.Y_to_Z).
now rewrite H0, H2 in H3.
pose (cone := commutative_pullback_square_to_cone D x (g >> pullback_to_a_mph p) (g >> pullback_to_b_mph p) H3).
pose (cone' := commutative_pullback_square_to_cone D x (g' >> pullback_to_a_mph p) (g' >> pullback_to_b_mph p) H4).
assert (cone = cone').
unfold cone, cone'. apply proof_irrelevance.
rewrite H0.

unfold is_pullback, is_limit, is_terminal in hyp_pullback. specialize (hyp_pullback cone). unfold universal_arrow in hyp_pullback.
destruct hyp_pullback as [phi].
pose (phi_g := pullback_morphism_to_cone_morphism D cone p g eq_refl eq_refl).
assert (phi_g = phi). exact (eq_sym (H4 phi_g)).




    

