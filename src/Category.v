Require Import FunctionalExtensionality.

(* Comment conserver les notations en dehors de la définition ?
   Utilise les univers polymorphiques pour permettre d'avoir une catégorie de catégories.
*)
Reserved Notation "a ~> b" (at level 90, right associativity).
Reserved Notation "f >> g" (at level 40, left associativity).

Polymorphic Class Category := {
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

Instance op_cat (C: Category) : Category.
apply (Build_Category ob (fun a b => b ~> a) id (fun _ _ _ f g => comp g f)) ; intros.
- apply cat_id_l.
- apply cat_id_r.
- apply eq_sym, cat_comp_assoc.
Defined.

Lemma cat_op_involutive (C: Category) : op_cat (op_cat C) = C.
unfold op_cat. destruct C. simpl. f_equal.
repeat (apply functional_extensionality_dep ; intro).
apply eq_sym_involutive.
Qed.

(* We should be able to avoid duplicates by defining duals with op_cat *)

Definition is_section    {C: Category} {a b: ob} (f: a ~> b) (g: b ~> a) := g >> f = id b.
Definition is_retraction {C: Category} {a b: ob} (f: a ~> b) (g: b ~> a) := f >> g = id a.
Definition is_inverse    {C: Category} {a b: ob} (f: a ~> b) (g: b ~> a) := is_section f g /\ is_retraction f g.

Definition is_mono {C: Category} {a b: ob} (f: a ~> b) :=
    forall (x: ob) (g g': x ~> a), (g >> f = g' >> f) -> (g = g').

Definition is_epi {C: Category} {a b: ob} (f: a ~> b) :=
    forall (x: ob) (g g': b ~> x), (f >> g = f >> g') -> (g = g').

Definition retraction_implies_mono {C: Category} {a b: ob} (f: a ~> b) (g: b ~> a) : is_retraction f g -> is_mono f.
unfold is_retraction, is_mono.
intros e_fg x h h' e_hf.
assert (hfg : h >> f >> g = h' >> f >> g).
now rewrite e_hf.
now rewrite !cat_comp_assoc, e_fg, !cat_id_r in hfg.
Qed.

Definition section_implies_epi {C: Category} {a b: ob} (f: a ~> b) (g: b ~> a) : is_section f g -> is_epi f.
unfold is_section, is_epi.
intros e_gh x h h' e_fh.
assert (hfg : g >> (f >> h) = g >> (f >> h')).
now rewrite e_fh.
now rewrite <-!cat_comp_assoc, e_gh, !cat_id_l in hfg.
Qed.
