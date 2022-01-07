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


Program Definition Cat : Category := {|
    ob := Obj;
    hom := Hom;
|}.
Next Obligation.
destruct a; now simpl. 
Qed.
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

Lemma nat_pullback {C : Category} {D : Pullback.Cat → C} (x : [C]) (f : x ~> ob[D] Pullback.X) (g : x ~> ob[D] Pullback.Y) : 
    (forall i j : [Pullback.Cat], forall u : i ~> j, tf_pullback x f g i >> hom[D] u = tf_pullback x f g j).
Proof.
intros. destruct i, j; simpl.
assert (u = id _). 
    
Definition commutative_pullback_square_to_cone {C : Category} (D : Pullback.Cat → C) (x : [C]) (f : x ~> ob[D] Pullback.X) (g : x ~> ob[D] Pullback.Y) 
    (commute : f >> hom[D] Pullback.X_to_Z = g >> hom[D] Pullback.Y_to_Z) : [cone_cat D].
Proof.
assert (forall i : [Pullback.Cat], x ~> ob[D] i) as tf.
intro. destruct i.
exact f.
exact g.
exact (f >> hom[D] Pullback.X_to_Z).
assert (forall i j : [Pullback.Cat], forall u : i ~> j, tf i >> hom[D] u = tf j) as nat.
intros. destruct i, j.

Lemma pullback_preserves_mono_b {C : Category} {D : Pullback.Cat → C} (p : [cone_cat D]) (is_pullback : is_pullback p) :
    forall u : Pullback.Hom Pullback.Y Pullback.Z, is_mono (hom[D] u) -> is_mono (pullback_to_a_mph p).
Proof.
intros. unfold is_mono. intros.
destruct u.
assert (g >> pullback_to_a_mph p >> (hom[D] Pullback.X_to_Z) = g' >> pullback_to_a_mph p >> (hom[D] Pullback.X_to_Z)).
now rewrite H0.
rewrite !cat_comp_assoc in H1.
rewrite (pullback_square_commute p) in H1.
assert (g >> pullback_to_b_mph p = g' >> pullback_to_b_mph p).
- rewrite <- !cat_comp_assoc in H1. unfold is_mono in H. now specialize (H x (g >> pullback_to_b_mph p) (g' >> pullback_to_b_mph p) H1).
-  

    

