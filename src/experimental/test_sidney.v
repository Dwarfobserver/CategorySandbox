
Require Import Category Functor dependent_records FunctionalExtensionality Setoid.

(* +----------------+
   | Slice category |
   +----------------+
*)

Module Slice.

Set Implicit Arguments.

Record slice_ob {C: Category} (c: ob) := {
    src : ob ;
    hom : src ~> c ;
}.

Record slice_hom {C: Category} (c: ob) (a b: slice_ob c) := {
    arr : src a ~> src b ;
    commute : hom a = arr >> hom b;
}.

Definition slice_id {C: Category} (c: ob) (a: slice_ob c) : slice_hom a a.
apply (Build_slice_hom _ _ (id (src a))).
apply eq_sym, cat_id_l.
Defined.

Definition slice_comp {C: Category} {c: ob} {x y z: slice_ob c}
    (f: slice_hom x y) (g: slice_hom y z) : slice_hom x z.
apply (Build_slice_hom _ _ (arr f >> arr g)).
rewrite (commute f).
rewrite (commute g).
apply eq_sym, cat_comp_assoc.
Defined.

Lemma slice_id_r {C: Category} {c: ob} {a b: slice_ob c} (f: slice_hom a b) :
    slice_comp f (slice_id b) = f.
unfold slice_id, slice_comp. simpl.

assert (e_arr : arr f >> id (src b) = arr f).
apply cat_id_r.
(* rewrite e_arr => coerce type stuff :( *)

Admitted.

Lemma slice_id_l {C: Category} {c: ob} {a b: slice_ob c} (f: slice_hom a b) :
    slice_comp (slice_id a) f = f.
Admitted.

Lemma slice_comp_assoc {C: Category} {c: ob} {x y z w: slice_ob c}
    (f: slice_hom x y) (g: slice_hom y z) (h: slice_hom z w) :
    slice_comp (slice_comp f g) h = slice_comp f (slice_comp g h).
Admitted.

Instance slice_cat {C: Category} (c: ob) : Category.
apply (Build_Category (slice_ob c) (@slice_hom C c) (@slice_id C c) (@slice_comp C c)) ; intros.
- apply slice_id_r.
- apply slice_id_l.
- apply slice_comp_assoc.
Defined.

Instance coslice_cat {C: Category} (c: ob) : Category := op_cat (slice_cat c).
(* Can prove theorems to simplify computation of under / coslice category. *)

End Slice.

(* +--------------------+
   | Discrete instances |
   +--------------------+
*)

Instance discrete_cat (T: Type) : Category.
apply (Build_Category T eq (@eq_refl T) (@eq_trans T)).
- apply eq_trans_refl_r.
- apply eq_trans_refl_l.
- intros. apply (eq_sym (eq_trans_assoc f g h)).
Defined.

Lemma cat_discrete_op_id T : op_cat (discrete_cat T) = discrete_cat T.
(* apply eq_category.

set (o1 := cat_oh_of (discrete_cat T)).
set (o2 := cat_oh_of (op_cat (discrete_cat T))).
assert (oH : o2 = o1).
unfold cat_oh_of in *. simpl in *.

change eq with (fun a b : T => a = b) in o1.
assert (e_hom : (fun a b : T => a = b) = (fun a b : T => b = a)).
repeat (apply functional_extensionality_dep ; intro).
apply (eq_sym x x0).
Admitted. *)

unfold op_cat, discrete_cat. simpl.
(* a=b   =   b=a ? *) 
Admitted.

Instance discrete_functor {A B} (f: A -> B) : Functor (discrete_cat A) (discrete_cat B).
apply (Build_Functor (discrete_cat A) (discrete_cat B) f (f_equal f)) ; simpl.
- reflexivity.
- intros. apply eq_trans_map_distr.
Defined.

Instance constant_functor (C D: Category) (d: @ob D) : Functor C D.
apply (Build_Functor C D (fun _ => d) (fun _ _ _ => @id _ d)).
- reflexivity.
- intros. apply (eq_sym (cat_id_r (@id _ d))).
Defined.
