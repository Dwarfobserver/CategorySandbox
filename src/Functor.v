Require Import Category FunctionalExtensionality Equality ProofIrrelevance.

Class Functor (C D: Category) := {
    f_ob : [C] -> [D] ;
    f_hom {a b: [C]} (f: a ~> b) : f_ob a ~> f_ob b ;

    f_id_distr (a: [C]) : f_hom (id a) = id (f_ob a) ;
    f_commute {a b c: [C]} (f: a ~> b) (g: b ~> c) :
        f_hom (f >> g) = (f_hom f) >> (f_hom g) ;
}.

Notation "C → D" := (Functor C D) (at level 90, right associativity).
Notation "ob[ F ]" := (@f_ob _ _ F) (at level 9, format "ob[ F ]").
Notation "hom[ F ]" := (@f_hom _ _ F _ _) (at level 9, format "hom[ F ]").

Record FunctorData (C D: Category) := {
  fdata_ob : [C] -> [D] ;
  fdata_hom {a b: [C]} (f: a ~> b) : fdata_ob a ~> fdata_ob b ;
}.
Definition functor_data_of {C D: Category} (F: C → D) := Build_FunctorData C D (@f_ob _ _ F) (@f_hom _ _ F).

Lemma functor_simpl_eq {C D: Category} (F G: C → D) :
  (functor_data_of F = functor_data_of G) -> F = G.
set (f := functor_data_of F).
set (g := functor_data_of G).
intro e. destruct F, G.
unfold functor_data_of, f_ob, f_hom in *. simpl. 

assert (e_ob : f_ob0 = f_ob1).
now dependent destruction e. destruct e_ob.
 
assert (e_hom : f_hom0 = f_hom1).
now dependent destruction e. destruct e_hom.

assert (e_dis: f_id_distr0 = f_id_distr1).
apply proof_irrelevance. destruct e_dis.

assert (e_comm: f_commute0 = f_commute1).
apply proof_irrelevance. destruct e_comm.

reflexivity.
Qed.

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
  forall (c c' : [C]) (f g : c ~> c'), f_hom f = f_hom g -> f = g.

Definition is_full {C D: Category} (F: Functor C D) :=
  forall (c c' : [C]) (g : f_ob c ~> f_ob c'), exists f : c ~> c', f_hom f = g.

Definition is_fully_faithful {C D: Category} (F: Functor C D) :=
  is_full F /\ is_faithful F.

Lemma functor_preserves_iso {C D: Category} (F: Functor C D) :
  forall (c c' : [C]) (f : c ~> c'), is_iso f -> is_iso (f_hom f).
Proof.
intros. unfold is_iso in *. destruct H as [f']. exists (f_hom f'). destruct H. split.
  - now rewrite <- f_commute, H, f_id_distr.
  - now rewrite <- f_commute, H0, f_id_distr.
Qed.

Lemma fully_faithful_injective_on_object {C D: Category} (F: C → D) (fully_faith_F : is_fully_faithful F):
  forall c c' : [C], ob[F] c ≃ ob[F] c' -> c ≃ c'.
Proof.
intros. destruct H as [f]. destruct fully_faith_F.
destruct (H0 c c' f) as [g]. exists g. destruct H as [f']. destruct (H0 c' c f') as [g']. 
exists g'. rewrite <- !H2, <- !H3, <- !f_commute, <- !f_id_distr in H. split; apply H1; easy.
Qed.

Lemma constant_functor_commute (C : Category) (c : [C]): id c = id c >> id c.
Proof.
  now rewrite cat_id_l.
Qed.

Definition constant_functor {I C : Category} (c : [C]) : I → C := {| 
  f_ob := fun _ => c;
  f_hom := fun _ _ _ => id c;

  f_id_distr := fun _ => eq_refl;
  f_commute := fun _ _ _ _ _ => constant_functor_commute C c;
|}.

Notation "Δ[ c ]" := (@constant_functor _ _ c) (at level 9).








