Require Import Category Functor FunctionalExtensionality ProofIrrelevance.
Require Import Coq.Program.Tactics Equality.

Class Transform {C D : Category} {F G : C → D} := {
    transform (x : [C]) : ob[F] x ~> ob[G] x; 

    naturality {a b : [C]} (f : a ~> b) : 
        hom[F] f >> transform b = transform a >> hom[G] f;
}.

Notation "F ⇒ G" := (@Transform _ _ F G) (at level 90, right associativity).
Notation "tf[ t ]" := (@transform _ _ _ _ t) (at level 9, format "tf[ t ]").
Notation "nat[ t ]" := (@naturality _ _ _ _ _ _ t) (at level 9, format "nat[ t ]").

Coercion transform : Transform >-> Funclass.

Lemma simpl_eq_transform {C D: Category} {F G: C → D} (S T: F ⇒ G) :
    tf[S] = tf[T] -> S = T.
destruct S, T. simpl.
intro eT. dependent destruction eT.
assert (eN: naturality0 = naturality1).
apply proof_irrelevance.
now destruct eN.
Qed.

Lemma compose_naturality {C D : Category} {F G H : C → D} {s : F ⇒ G} {t : G ⇒ H} {a b : [C]} (f : a ~> b) :
hom[F] f >> (tf[s] b >> tf[t] b) = (tf[s] a >> tf[t] a) >> hom[H] f.
Proof.
now rewrite cat_comp_assoc, <- naturality, <- (cat_comp_assoc _ (hom[G] f) _), <- naturality, cat_comp_assoc.
Qed.

Definition compose_transform {C D : Category} {F G H : C → D} (s : F ⇒ G) (t : G ⇒ H) : F ⇒ H := {| 
    transform (x : [C]) := (tf[s] x) >> (tf[t]) x;
    naturality := @compose_naturality _ _ _ _ _ s t;
|}.

Notation "s # t" := (compose_transform s t) (at level 40, left associativity). 

Lemma id_transform_naturality {C D : Category} {F : C → D} {a b : [C]} (f : a ~> b) : 
    hom[F] f >> hom[F] (id b) = hom[F] (id a) >> hom[F] f.
Proof.
    now rewrite <- !f_commute, cat_id_r, cat_id_l.
Qed.

Definition id_transform {C D : Category} {F : C → D} : F ⇒ F := {|
    transform (x : [C]) := hom[F] (id x);
    naturality := @id_transform_naturality C D F;
|}.
Notation "id_nat[ F ]" := (@id_transform _ _ F) (at level 9, format "id_nat[ F ]").

Lemma id_transform_id_l {C D : Category} {F G : C → D} (t : F ⇒ G) : id_nat[F] # t = t.
Proof.
apply simpl_eq_transform.
unfold id_transform, compose_transform. simpl.
apply functional_extensionality_dep. intro. now rewrite f_id_distr, cat_id_l.
Qed.

Lemma id_transform_id_r {C D : Category} {F G : C → D} (t : F ⇒ G) : t # id_nat[G] = t.
Proof.
apply simpl_eq_transform.
unfold id_transform, compose_transform. simpl.
apply functional_extensionality_dep. intro. now rewrite f_id_distr, cat_id_r.
Qed.

Lemma transform_comp_assoc {C D: Category} {F G H I: Functor C D} (R : F ⇒ G) (S : G ⇒ H) (T : H ⇒ I) :
    (R # S) # T = R # (S # T).
Proof.
apply simpl_eq_transform.
unfold compose_transform. simpl.
apply functional_extensionality_dep. intro. now rewrite cat_comp_assoc.
Qed.

Definition functor_category (C D : Category) : Category := {|
    ob := C → D;
    hom F G := F ⇒ G;
    id F := id_nat[F];
    comp := fun _ _ _ s t => s # t;

    cat_id_r := @id_transform_id_r C D;
    cat_id_l := @id_transform_id_l C D;
    cat_comp_assoc := @transform_comp_assoc C D;
|}.

Notation "[ C , D ]" := (functor_category C D). 

(*
Program Definition functor_transform {C D E : Category} {G H : D → E} (F : C → D) (t : G ⇒ H) : F >>> G ⇒ F >>> H := {|
    transform (x : [C]) := tf[t] (ob[F] x);
|}.
Next Obligation. 

rewrite <- !functor_comp_commute_mph.
*)