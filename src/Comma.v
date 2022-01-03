Require Import Category Functor Transform Limit Equality ProofIrrelevance.

Module Comma.

Set Implicit Arguments.

Class comma_ob {A B C : Category} (S : A → C) (T : B → C) := {
    dom : [A];
    cod : [B];
    mph : ob[S] dom ~> ob[T] cod;
}.

Notation "dom[ c ]" := (@dom _ _ _ _ _ c) (at level 9).
Notation "cod[ c ]" := (@cod _ _ _ _ _ c) (at level 9).
Notation "mph[ c ]" := (@mph _ _ _ _ _ c) (at level 9).

Class comma_mph {A B C : Category} {S : A → C} {T : B → C} (t t' : comma_ob S T) := {
    source_mph : dom[t] ~> dom[t'];
    target_mph : cod[t] ~> cod[t'];
    commute : hom[S] source_mph >> mph[t'] = mph[t] >> hom[T] target_mph;
}.

Notation "source[ f ]" := (@source_mph _ _ _ _ _ _ _ f) (at level 9).
Notation "target[ f ]" := (@target_mph _ _ _ _ _ _ _ f) (at level 9).
Notation "commute[ f ]" := (@commute _ _ _ _ _ _ _ f) (at level 9).

Lemma comma_hom_simpl_eq {A B C: Category} {S: A → C} {T: B → C} {t t': comma_ob S T} (f g: comma_mph t t') :
    source[f] = source[g] -> target[f] = target[g] -> f = g.
destruct f, g. simpl.
intros eS eT.
destruct eS, eT.
assert (eC: commute0 = commute1).
apply proof_irrelevance.
now destruct eC.
Qed.

Program Definition comma_id {A B C: Category} {S: A → C} {T: B → C} (c: comma_ob S T) := {|
    source_mph := id (dom[c]);
    target_mph := id (cod[c]);
|}.
Next Obligation.
now rewrite !f_id_distr, cat_id_l, cat_id_r.
Defined.

Program Definition comma_comp {A B C: Category} {S: A → C} {T: B → C} {r s t: comma_ob S T}
    (f: comma_mph r s) (g: comma_mph s t) :=
{|
    source_mph := source[f] >> source[g];
    target_mph := target[f] >> target[g];
|}.
Next Obligation.
rewrite !f_commute.
rewrite <-cat_comp_assoc, cat_comp_assoc.
rewrite <-(commute[f]), (commute[g]).
now rewrite cat_comp_assoc.
Qed.

Lemma comma_id_r {A B C: Category} {S: A → C} {T: B → C} {s t: comma_ob S T} (f: comma_mph s t) : comma_comp f (comma_id _) = f.
apply comma_hom_simpl_eq ; simpl ; now rewrite cat_id_r.
Qed.

Lemma comma_id_l {A B C: Category} {S: A → C} {T: B → C} {s t: comma_ob S T} (f: comma_mph s t) : comma_comp (comma_id _) f = f.
apply comma_hom_simpl_eq ; simpl ; now rewrite cat_id_l.
Qed.

Lemma comma_comp_assoc {A B C: Category} {S: A → C} {T: B → C} {q r s t: comma_ob S T}
    (f: comma_mph q r) (g: comma_mph r s) (h: comma_mph s t) : comma_comp (comma_comp f g) h = comma_comp f (comma_comp g h).
apply comma_hom_simpl_eq ; simpl ; now rewrite cat_comp_assoc.
Qed.

End Comma.

Definition comma_cat {A B C : Category} (S : A → C) (T : B → C) : Category.
apply (Build_Category (Comma.comma_ob S T) Comma.comma_mph (fun x => Comma.comma_id x) (fun _ _ _ x y => Comma.comma_comp x y)) ; intros.
- apply Comma.comma_id_r.
- apply Comma.comma_id_l.
- apply Comma.comma_comp_assoc.
Defined.
