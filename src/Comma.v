Require Import Category Functor Transform Limit.

Class comma_ob {A B C : Category} (S : A → C) (T : B → C) := {
    dom : [A];
    cod : [B];
    mph : ob[S] dom ~> ob[T] cod;
}.

Notation "dom[ c ]" := (@dom _ _ _ _ _ c) (at level 9).
Notation "cod[ c ]" := (@cod _ _ _ _ _ c) (at level 9).
Notation "mph[ c ]" := (@mph _ _ _ _ _ c) (at level 9).

Class comma_mph {A B C : Category} (S : A → C) (T : B → C) (t t' : comma_ob S T) := {
    source_mph : dom[t] ~> dom[t'];
    target_mph : cod[t] ~> cod[t'];
    commute : hom[S] source_mph >> mph[t'] = mph[t] >> hom[T] target_mph;
}.

Notation "source[ t , t' ]" := (@source_mph _ _ _ _ _ t t') (at level 9).
Notation "target[ t , t' ]" := (@source_mph _ _ _ _ _ t t') (at level 9).
Notation "commute[ t , t' ]" := (@source_mph _ _ _ _ _ t t') (at level 9).

Program Definition comma_id {A B C : Category} (S : A → C) (T : B → C) (c : comma_ob S T) := {|
    source_mph := id (dom[c]);
    target_mph := id (cod[c]);
|}.
Next Obligation.
now rewrite !f_id_distr, cat_id_l, cat_id_r.
Qed.

Program Definition comp_comma_mph {A B C : Category} (S : A → C) (T : B → C) ():= .

Definition comma_cat {A B C : Category} (S : A → C) (T : B → C) : Category := {|
    ob := ()
|}.
