Require Import Category Functor Transform Equality ProofIrrelevance FunctionalExtensionality.

Module Comma.

Set Implicit Arguments.

Class comma_ob {A B C : Category} (S : A → C) (T : B → C) := {
    dom : [A];
    cod : [B];
    mph : ob[S] dom ~> ob[T] cod;
}.

Notation "dom[ c ]" := (@dom _ _ _ _ _ c) (at level 9).
Notation "cod[ c ]" := (@cod _ _ _ _ _ c) (at level 9).
Notation "mph[ c ]" := (@mph _ _ _ _ _ c) (at level 9).

Class comma_mph {A B C : Category} {S : A → C} {T : B → C} (t t' : comma_ob S T) := {
    source_mph : dom[t] ~> dom[t'];
    target_mph : cod[t] ~> cod[t'];
    commute : hom[S] source_mph >> mph[t'] = mph[t] >> hom[T] target_mph;
}.

Notation "source[ f ]" := (@source_mph _ _ _ _ _ _ _ f) (at level 9).
Notation "target[ f ]" := (@target_mph _ _ _ _ _ _ _ f) (at level 9).
Notation "commute[ f ]" := (@commute _ _ _ _ _ _ _ f) (at level 9).

Lemma comma_hom_simpl_eq {A B C: Category} {S: A → C} {T: B → C} {t t': comma_ob S T} (f g: comma_mph t t') :
    source[f] = source[g] -> target[f] = target[g] -> f = g.
destruct f, g. simpl.
intros eS eT.
destruct eS, eT.
assert (eC: commute0 = commute1).
apply proof_irrelevance.
now destruct eC.
Qed.

Program Definition comma_id {A B C: Category} {S: A → C} {T: B → C} (c: comma_ob S T) := {|
    source_mph := id (dom[c]);
    target_mph := id (cod[c]);
|}.
Next Obligation.
now rewrite !f_id_distr, cat_id_l, cat_id_r.
Defined.

Program Definition comma_comp {A B C: Category} {S: A → C} {T: B → C} {r s t: comma_ob S T}
    (f: comma_mph r s) (g: comma_mph s t) :=
{|
    source_mph := source[f] >> source[g];
    target_mph := target[f] >> target[g];
|}.
Next Obligation.
rewrite !f_commute.
rewrite <-cat_comp_assoc, cat_comp_assoc.
rewrite <-(commute[f]), (commute[g]).
now rewrite cat_comp_assoc.
Qed.

Lemma comma_id_r {A B C: Category} {S: A → C} {T: B → C} {s t: comma_ob S T} (f: comma_mph s t) : comma_comp f (comma_id _) = f.
apply comma_hom_simpl_eq ; simpl ; now rewrite cat_id_r.
Qed.

Lemma comma_id_l {A B C: Category} {S: A → C} {T: B → C} {s t: comma_ob S T} (f: comma_mph s t) : comma_comp (comma_id _) f = f.
apply comma_hom_simpl_eq ; simpl ; now rewrite cat_id_l.
Qed.

Lemma comma_comp_assoc {A B C: Category} {S: A → C} {T: B → C} {q r s t: comma_ob S T}
    (f: comma_mph q r) (g: comma_mph r s) (h: comma_mph s t) : comma_comp (comma_comp f g) h = comma_comp f (comma_comp g h).
apply comma_hom_simpl_eq ; simpl ; now rewrite cat_comp_assoc.
Qed.

End Comma.

Definition comma_cat {A B C: Category} (S: A → C) (T: B → C) : Category.
apply (Build_Category (Comma.comma_ob S T) Comma.comma_mph (fun x => Comma.comma_id x) (fun _ _ _ x y => Comma.comma_comp x y)) ; intros.
- apply Comma.comma_id_r.
- apply Comma.comma_id_l.
- apply Comma.comma_comp_assoc.
Defined.

(* Need shortcuts to be really usable *)
Definition cone_cat {I C: Category} (D: I → C) : Category := comma_cat delta_functor (unit_curry D).

(* 
    Here, an object in cone_cat D is a triple (c : [C], unit, t : Δc ⥰ D)
    Let's make sure we can retrieve this data easily
*)
Definition cone_base {I C: Category} {D: I → C} (d : [cone_cat D]) : [C] := @Comma.dom _ _ _ _ _ d.
Definition cone_transform {I C: Category} {D: I → C} (d : [cone_cat D]) : Δ[cone_base d] ⇒ D := @Comma.mph _ _ _ _ _ d.

Lemma cone_naturality {I C: Category} {D: I → C} {i j : [I]} (d : [cone_cat D]) (u : i ~> j) : 
    tf[cone_transform d] i >> hom[D] u = tf[cone_transform d] j.
Proof.
rewrite <- (nat[cone_transform d, u]). simpl. now rewrite cat_id_l.
Qed.


Program Definition construct_cone_transform {I C: Category} {D: I → C} 
    (c : [C]) (tf : forall i : [I], c ~> ob[D] i)
    (nat : forall i j, forall u : i ~> j, tf i >> hom[D] u = tf j) : Δ[c] ⇒ D := {| 
        transform := tf;
    |}.
Next Obligation.
rewrite cat_id_l. apply eq_sym. apply (nat a b f).
Defined.

Program Definition construct_cone {I C: Category} {D: I → C} 
    (base : [C]) (tf : forall i : [I], base ~> ob[D] i)
    (nat : forall i j, forall u : i ~> j, tf i >> hom[D] u = tf j) : [cone_cat D] := {| 
        Comma.dom := base;
        Comma.cod := tt; 
    |}.
Next Obligation.
exact (construct_cone_transform base tf nat).
Defined.

(* A morphism of cone is morally a morphism in the category C s.t. all triangles commute *)
Program Definition morphism_to_cone_morphism {I C: Category} {D: I → C} (p1 p2 : [cone_cat D]) (f : cone_base p1 ~> cone_base p2)
(nat : forall i : [I], tf[cone_transform p1] i = f >> tf[cone_transform p2] i) : p1 ~> p2 := {|
    Comma.source_mph := f;
    Comma.target_mph := tt;
|}.
Next Obligation. 
rewrite id_transform_id_r. apply transform_simpl_eq. apply functional_extensionality_dep. intro.
unfold compose_transform. simpl. specialize (nat x). unfold constant_transform_tf. apply eq_sym. assumption.
Defined.

Definition cone_mph_to_induced_mph {I C: Category} {D: I → C} {p1 p2 : [cone_cat D]} (phi : p1 ~> p2) : 
    (cone_base p1 ~> cone_base p2) := @Comma.source_mph _ _ _ _ _ p1 p2 phi.

Lemma same_cone_morphism_same_induced_morphism {I C: Category} {D: I → C} (p1 p2 : [cone_cat D]) (phi phi' : p1 ~> p2) :
    phi = phi' -> cone_mph_to_induced_mph phi = cone_mph_to_induced_mph phi'.
Proof.
intro. now rewrite H.
Qed.