Require Import Category FunctionalExtensionality.

Class Functor (C D: Category) := {
    f_ob : (@ob C) -> (@ob D) ;
    f_hom {a b: @ob C} (f: a ~> b) : f_ob a ~> f_ob b ;

    f_id_distr (a: @ob C) : f_hom (id a) = id (f_ob a) ;
    f_commute {a b c: @ob C} (f: a ~> b) (g: b ~> c) :
        f_hom (f >> g) = (f_hom f) >> (f_hom g) ;
}.

Instance id_functor (C: Category) : Functor C C.
apply (Build_Functor C C (fun x => x) (fun _ _ f => f)).
- reflexivity.
- reflexivity.
Defined.

Definition comp_functor {C D E: Category} (F: Functor C D) (G: Functor D E) : Functor C E.
apply (Build_Functor C E (fun c => f_ob (f_ob c)) (fun _ _ f => f_hom (f_hom f))).
(* Applying when possible instead of rewriting to define simpler lambda-terms *)
- intros. rewrite f_id_distr. apply f_id_distr.
- intros. rewrite f_commute. apply f_commute.
Defined.
Notation "f >>> g" := (comp_functor f g) (at level 40, left associativity).

Lemma functor_id_r {C D: Category} (F: Functor C D) : F >>> id_functor D = F.
unfold comp_functor, id_functor. destruct F. simpl. f_equal.
- apply functional_extensionality_dep. intro. now rewrite f_id_distr0.
- repeat (apply functional_extensionality_dep ; intro). now rewrite f_commute0.
Qed.

Lemma functor_id_l {C D: Category} (F: Functor C D) : id_functor C >>> F = F.
unfold comp_functor, id_functor. destruct F. simpl. f_equal.
Qed.

Lemma functor_comp_assoc {A B C D: Category} (F: Functor A B) (G: Functor B C) (H: Functor C D) :
    (F >>> G) >>> H = F >>> (G >>> H).
unfold comp_functor, id_functor. destruct F, G, H. simpl. f_equal.
- apply functional_extensionality_dep. intro x. unfold eq_ind_r, eq_ind, eq_sym.
  now rewrite f_id_distr0, f_id_distr1.
- repeat (apply functional_extensionality_dep ; intro). unfold eq_ind_r, eq_ind, eq_sym.
  now rewrite f_commute0, f_commute1.
Qed.
