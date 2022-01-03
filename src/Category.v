Require Import FunctionalExtensionality.

(* Comment conserver les notations en dehors de la définition ?
   Utilise les univers polymorphiques pour permettre d'avoir une catégorie de catégories.
*)
Reserved Notation "a ~> b" (at level 90, right associativity).
Reserved Notation "f >> g" (at level 40, left associativity).
Reserved Notation "a ≃ b" (at level 90, right associativity).

Cumulative Polymorphic Class Category := {
    ob : Type;
    hom : ob -> ob -> Type where "a ~> b" := (hom a b);
    id (a: ob) : a~>a;
    comp {a b c: ob} : a~>b -> b~>c -> a~>c where "f >> g" := (comp f g);

    cat_id_r {a b: ob} (f: a~>b) : f >> (id b) = f;
    cat_id_l {a b: ob} (f: a~>b) : (id a) >> f = f;
    cat_comp_assoc {a b c d: ob} (f: a~>b) (g: b~>c) (h: c~>d) : (f >> g) >> h = f >> (g >> h);
}.
Notation "a ~> b" := (hom a b).
Notation "f >> g" := (comp f g).
Notation "[ C ]" := (@ob C) (at level 90, no associativity).

Instance op_cat (C: Category) : Category.
apply (Build_Category ob (fun a b => b ~> a) id (fun _ _ _ f g => comp g f)) ; intros.
- apply cat_id_l.
- apply cat_id_r.
- apply eq_sym, cat_comp_assoc.
Defined.

Notation "C ^op" := (op_cat C) (at level 9, no associativity).

Lemma cat_op_involutive (C: Category) : (C^op)^op = C.
unfold op_cat. destruct C. simpl. f_equal.
repeat (apply functional_extensionality_dep ; intro).
apply eq_sym_involutive.
Qed.

Instance unit_cat : Category.
apply (Build_Category unit (fun _ _ => unit) (fun x => x) (fun _ _ _ _ _ => tt))
  ; intros ; induction f ; trivial.
Defined.

Notation "'*" := unit_cat (at level 5, no associativity).

(* We should be able to avoid duplicates by defining duals with op_cat *)

Definition is_section    {C: Category} {a b: ob} (f: a ~> b) (g: b ~> a) := g >> f = id b.
Definition is_retraction {C: Category} {a b: ob} (f: a ~> b) (g: b ~> a) := f >> g = id a.
Definition is_inverse    {C: Category} {a b: ob} (f: a ~> b) (g: b ~> a) := is_section f g /\ is_retraction f g.

Definition is_mono {C: Category} {a b: ob} (f: a ~> b) :=
    forall (x: ob) (g g': x ~> a), (g >> f = g' >> f) -> (g = g').

Definition is_epi {C: Category} {a b: ob} (f: a ~> b) :=
    forall (x: ob) (g g': b ~> x), (f >> g = f >> g') -> (g = g').

Definition is_iso {C: Category} {a b: ob} (f: a ~> b) := 
    exists g : b ~> a, (f >> g = id a) /\ (g >> f = id b).

Lemma retraction_implies_mono {C: Category} {a b: ob} (f: a ~> b) (g: b ~> a) : is_retraction f g -> is_mono f.
Proof.
unfold is_retraction, is_mono.
intros e_fg x h h' e_hf.
assert (hfg : h >> f >> g = h' >> f >> g).
now rewrite e_hf.
now rewrite !cat_comp_assoc, e_fg, !cat_id_r in hfg.
Qed.

Lemma section_implies_epi {C: Category} {a b: ob} (f: a ~> b) (g: b ~> a) : is_section f g -> is_epi f.
Proof.
unfold is_section, is_epi.
intros e_gh x h h' e_fh.
assert (hfg : g >> (f >> h) = g >> (f >> h')).
now rewrite e_fh.
now rewrite <-!cat_comp_assoc, e_gh, !cat_id_l in hfg.
Qed.

Lemma iso_to_mono {C: Category} {a b: ob} (f: a ~> b) (h : is_iso f) : is_mono f.
Proof.
unfold is_mono. intros. destruct h as [f']. destruct H0.
now rewrite <- cat_id_r, <- (cat_id_r g), <- H0, <- cat_comp_assoc, H, cat_comp_assoc.
Qed.

Lemma iso_to_epi {C: Category} {a b: ob} (f: a ~> b) (h : is_iso f) : is_epi f.
Proof. 
unfold is_epi. intros. destruct h as [f']. destruct H0.
now rewrite <- cat_id_l, <- (cat_id_l g), <- H1, cat_comp_assoc, H, <- cat_comp_assoc.
Qed.

Lemma comp_iso_is_iso {C: Category} {a b c : ob} (f: a ~> b) (g : b ~> c) (iso_f : is_iso f) (iso_g : is_iso g) :
    is_iso (f >> g).
Proof.
destruct iso_f as [f']. destruct iso_g as [g']. exists (g' >> f'). destruct H, H0.
rewrite cat_comp_assoc, cat_comp_assoc, <- (cat_comp_assoc _ g' _), <- (cat_comp_assoc _ f _), H0, H1.
now rewrite !cat_id_l, H, H2.
Qed.

Definition ob_isom {C: Category} (a b: ob) := exists g : a ~> b, is_iso g.
Notation "a ≃ b" := (ob_isom a b) (at level 90, right associativity).

Lemma isom_sym {C: Category} (a b: ob) : a ≃ b -> b ≃ a.
Proof.
intro. destruct H as [f]. destruct H as [f']. exists f'. unfold is_iso. exists f. easy.
Qed.

Lemma iso_refl {C: Category} (a : ob) : a ≃ a.
Proof.
exists (id a). unfold is_iso. exists (id a). 
now rewrite !cat_id_l.
Qed.

Lemma iso_trans {C: Category} (a b c : ob) : a ≃ b -> b ≃ c -> a ≃ c.
Proof.
intros. destruct H as [f], H0 as [g]. exists (f >> g). 
now apply comp_iso_is_iso.
Qed.

Definition is_inv {C: Category} {a b: ob} (f: a ~> b) (g : b ~> a ):= f >> g = id a /\ g >> f = id b.

Lemma unique_inv {C: Category} {a b: ob} (f: a ~> b) (g h: b ~> a ) : 
    is_inv f g -> is_inv f h -> g = h.
Proof.
intros. destruct H, H0. 
now rewrite <- cat_id_r, <- H, <- cat_comp_assoc, H2, cat_id_l.
Qed.

Lemma op_isom_iff_isom {C: Category} (a b: [C]) :
    @ob_isom C^op a b <-> a ≃ b.
Proof.
split; intro; destruct H as [f]; destruct H as [f']; exists f'; unfold is_iso; exists f; easy.
Qed.
