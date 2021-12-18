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

Instance op_cat (C: Category) : Category. (* Comment pouvoir juste utiliser 'id' > *)
apply (Build_Category ob (fun a b => b ~> a) id (fun _ _ _ f g => comp g f)) ; intros.
- apply cat_id_l.
- apply cat_id_r.
- apply (eq_sym (cat_comp_assoc h g f)).
Defined.

Lemma cat_op_involutive (C: Category) : op_cat (op_cat C) = C.
unfold op_cat. destruct C. simpl. f_equal.
repeat (apply functional_extensionality_dep ; intro).
apply eq_sym_involutive.
Qed.
