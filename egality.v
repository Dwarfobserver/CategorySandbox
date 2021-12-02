Reserved Infix "≃" (at level 70).


Inductive cat_eq {A : Type} (f g : A -> Type) : Prop :=
    | eq  : f = g -> cat_eq f g
    | ext : (forall a, eq (f a) (g a)) -> cat_eq f g.

Notation "f ≃ g" := (cat_eq f g).

Lemma cat_eq_sym_aux {A : Type} (f g : A -> Type) : f ≃ g -> g ≃ f.
Proof.
    intro. induction H.
    - now apply eq.
    - apply ext. intro. symmetry. exact (H a).
Qed.

Lemma cat_eq_sym {A : Type} (f g : A -> Type) : f ≃ g <-> g ≃ f.
Proof.
    split; now apply cat_eq_sym_aux.
Qed.

Lemma cat_eq_refl {A : Type} (f : A -> Type) : f ≃ f.
Proof.
    now apply eq.
Qed.

Lemma cat_eq_trans {A : Type} (f g h : A -> Type) : f ≃ g -> g ≃ h -> f ≃ h.
Proof.
    intros. induction H.
    - now rewrite <- H in H0.
    - induction H0.
        + rewrite H0 in H. now apply ext.
        + apply ext. congruence.
Qed.

    

    


 