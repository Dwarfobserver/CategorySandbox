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


Definition is_faithful {C D: Category} (F: Functor C D) := 
  forall (c c' : @ob C) (f g : c ~> c'), f_hom f = f_hom g -> f = g.

Definition is_full {C D: Category} (F: Functor C D) :=
  forall (c c' : @ob C) (g : f_ob c ~> f_ob c'), exists f : c ~> c', f_hom f = g.
  
Definition is_fully_faithful {C D: Category} (F: Functor C D) :=
  is_full F /\ is_faithful F.

Lemma functor_preserves_iso {C D: Category} (F: Functor C D) :
  forall (c c' : @ob C) (f : c ~> c'), is_iso f -> is_iso (f_hom f).
Proof.
intros. unfold is_iso in *. destruct H as [f']. exists (f_hom f'). destruct H. split.
  - now rewrite <- f_commute, H, f_id_distr.
  - now rewrite <- f_commute, H0, f_id_distr.
Qed.

Lemma fully_faithful_injective_on_object {C D: Category} (F: Functor C D) (fully_faith_F : is_fully_faithful F):
  forall c c' : @ob C, f_ob c ≃ f_ob c' -> c ≃ c'.
Proof.
intros. destruct H as [f]. destruct fully_faith_F.
destruct (H0 c c' f) as [g]. exists g. destruct H as [f']. destruct (H0 c' c f') as [g']. 
exists g'. rewrite <- !H2, <- !H3, <- !f_commute, <- !f_id_distr in H. split; apply H1; easy.
Qed.






