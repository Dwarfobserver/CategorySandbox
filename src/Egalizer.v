Require Import Category Functor Transform Comma Limit.
Require Import Equality ProofIrrelevance.


Module Egalizer.

(*
    Egalizer diagram :
        UP
       ------->
    X           Y
       ------->
        DOWN
*)

Inductive Obj := X | Y.

Inductive Empty : Set :=.
Inductive One : Set := ID.
Inductive Two : Set := UP | DOWN.

Definition Hom (x y : Obj) := 
    match x, y with
    | X, X => One
    | Y, Y => One
    | X, Y => Two
    | Y, X => Empty
    end.

Definition Id (x : Obj) : Hom x x.
destruct x; now simpl.
Defined.

Program Definition Cat : Category := {|
    ob := Obj;
    hom := Hom;
    id  := Id;
|}.
Next Obligation.
destruct a, b, c; now simpl.
Defined.
Next Obligation.
destruct a, b; simpl; now destruct f.
Defined.
Next Obligation.
destruct a, b; now simpl.
Defined.
Next Obligation.
destruct a, b, c, d, f, g, h; now simpl.
Defined.

Definition UP_mph : @hom Cat X Y := UP.
Definition DOWN_mph : @hom Cat X Y := DOWN.

Definition diagram_ob {C : Category} (a b : [C]) (x : Obj) : [C] := 
    match x with
    | X => a
    | Y => b
    end.

Definition diagram_hom {C : Category} {a b : [C]} (f g : a ~> b) (x y : Obj) (t : Hom x y) := 
    match x, y, t return diagram_ob a b x ~> diagram_ob a b y with
    | X, X, _    => id a
    | Y, Y, _    => id b
    | X, Y, UP   => f
    | X, Y, DOWN => g
    | _, _, t    => match t with end
    end.

Program Definition construct_diagram {C : Category} {a b : [C]} (f g : a ~> b) : Cat → C := {|
    f_ob := diagram_ob a b;
    f_hom := diagram_hom f g
|}.
Next Obligation.
destruct a0; now simpl.
Defined.
Next Obligation.
destruct a0, b0, c; simpl; try rewrite cat_id_l; try rewrite cat_id_r; now simpl.
Defined.

End Egalizer.

Definition is_egalizer {C : Category} {D : Egalizer.Cat → C} (p : [cone_cat D]) := is_limit p.

Definition egalizer_obj {C : Category} {D : Egalizer.Cat → C} (p : [cone_cat D]) : [C] := cone_base p.

Definition egalizer_mph {C : Category} {D : Egalizer.Cat → C} (p : [cone_cat D]) : egalizer_obj p ~> ob[D] Egalizer.X := 
    tf[cone_transform p] Egalizer.X.

Lemma egalizer_egalize {C : Category} {D : Egalizer.Cat → C} (p : [cone_cat D]) :
    egalizer_mph p >> hom[D] Egalizer.UP_mph = egalizer_mph p >> hom[D] Egalizer.DOWN_mph.
Proof.
assert (egalizer_mph p >> hom[D] Egalizer.UP_mph = tf[cone_transform p] Egalizer.X >> hom[D] Egalizer.UP_mph).
reflexivity. 
rewrite H, (cone_naturality p Egalizer.UP_mph).
assert (egalizer_mph p >> hom[D] Egalizer.DOWN_mph = tf[cone_transform p] Egalizer.X >> hom[D] Egalizer.DOWN_mph).
reflexivity.
now rewrite H0, (cone_naturality p Egalizer.DOWN_mph).
Qed.


Definition tf_egalizer {C : Category} {D : Egalizer.Cat → C} (x : [C]) (f : x ~> ob[D] Egalizer.X) :=  
    fun i : [Egalizer.Cat] =>    
        match i with
        | Egalizer.X => f
        | Egalizer.Y => f >> hom[D] Egalizer.UP_mph
        end.

Lemma nat_egalizer {C : Category} {D : Egalizer.Cat → C} (x : [C]) (f : x ~> ob[D] Egalizer.X) 
(nat : f >> hom[D] Egalizer.UP_mph = f >> hom[D] Egalizer.DOWN_mph) : 
    (forall i j : [Egalizer.Cat], forall u : i ~> j, tf_egalizer x f i >> hom[D] u = tf_egalizer x f j).
Proof.
intros. destruct i, j, u; simpl.
- now rewrite (@f_id_distr Egalizer.Cat), cat_id_r. 
- reflexivity.
- now rewrite nat.
- now rewrite (@f_id_distr Egalizer.Cat), cat_id_r.
Qed.

(* If an arrow egalize UP and DOWN, then we can make a cone *)
Definition egalize_mph_to_cone {C : Category} (D : Egalizer.Cat → C) (x : [C]) (f : x ~> ob[D] Egalizer.X) 
    (nat : f >> hom[D] Egalizer.UP_mph = f >> hom[D] Egalizer.DOWN_mph) : [cone_cat D].
exact (@construct_cone Egalizer.Cat C D x (tf_egalizer x f) (nat_egalizer x f nat)).
Defined.

Lemma naturality_egalizer_morphism {C : Category} {D : Egalizer.Cat → C} (p1 p2 : [cone_cat D]) (mph : cone_base p1 ~> cone_base p2) 
(nat : mph >> egalizer_mph p2 = egalizer_mph p1) :
    forall i : [Egalizer.Cat], tf[cone_transform p1] i = mph >> tf[cone_transform p2] i.
Proof.
intro. destruct i; unfold egalizer_mph in nat.
- exact (eq_sym nat).
- now rewrite <- (cone_naturality p2 Egalizer.UP_mph), <- cat_comp_assoc, nat, <- (cone_naturality p1 Egalizer.UP_mph).
Qed. 

(* If an arrow commute with the egalizer morphism, it can create a cone morphism *)
Definition pullback_morphism_to_cone_morphism {C : Category} (D : Egalizer.Cat → C) (p1 p2 : [cone_cat D]) (mph : cone_base p1 ~> cone_base p2)
    (nat : mph >> egalizer_mph p2 = egalizer_mph p1) : p1 ~> p2 := 
    morphism_to_cone_morphism p1 p2 mph (naturality_egalizer_morphism p1 p2 mph nat).

Lemma egalizer_mono {C : Category} {D : Egalizer.Cat → C} (p : [cone_cat D]) :
    is_egalizer p -> is_mono (egalizer_mph p).
Proof.
unfold is_mono. intros H x g g' H_eq.
assert (g >> egalizer_mph p >> hom[D] Egalizer.UP_mph = g >> egalizer_mph p >> hom[D] Egalizer.DOWN_mph).
now rewrite !cat_comp_assoc, egalizer_egalize. 
pose (cone := egalize_mph_to_cone D x (g >> egalizer_mph p) H0).
unfold is_egalizer, is_limit, is_terminal, universal_arrow in H.
specialize (H cone). destruct H as [phi].
pose (phi_g := pullback_morphism_to_cone_morphism D cone p g eq_refl).
pose (phi_g' := pullback_morphism_to_cone_morphism D cone p g' (eq_sym H_eq)).
assert (phi_g = phi_g'). now rewrite <- (H phi_g), (H phi_g').
assert (cone_mph_to_induced_mph phi_g = cone_mph_to_induced_mph phi_g').
now apply same_cone_morphism_same_induced_morphism.
exact H2.
Qed.





