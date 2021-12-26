Require Import Category Functor FunctionalExtensionality.

Class Natural_Transformation {C D: Category} (F G: Functor C D) := {
    n_ob (a: @ob C) : (@f_ob _ _ F a) ~> (@f_ob _ _ G a);
    n_commute {a b: @ob C} (f: a ~> b) :
        let Ff := (@f_hom _ _ F _ _ f) in
        let Gf := (@f_hom _ _ G _ _ f) in
        Ff >> n_ob b = n_ob a >> Gf ;
}.

Instance id_nat_tr {C D: Category} (F: Functor C D) : Natural_Transformation F F.
apply (Build_Natural_Transformation _ _ _ _ (fun a => @id _ (f_ob a))).
intros.
rewrite cat_id_r, cat_id_l. reflexivity.
Defined.

Instance comp_nat_tr {C D: Category} {F G H: Functor C D}
    (S: Natural_Transformation F G) (T: Natural_Transformation G H) : Natural_Transformation F H.
destruct S as [Smap Scommute], T as [Tmap Tcommute].
apply (Build_Natural_Transformation _ _ _ _ (fun a => (Smap a) >> (Tmap a))).
intros. rename Gf into Hf.
set (Gf := @f_hom _ _ G _ _ f).

(* Prouve la naturalité en passant par le chemin du milieu. *)

(* Pourquoi les rewrite ne fonctionnent plus avec une variable (comme p_half) ?
set (p_begin := Ff >> Smap b >> Tmap b).
set (p_half  := Smap a >> Gf >> Tmap b).
set (p_end   := Smap a >> (Tmap a >> Hf)). *)
assert (H0 : Ff >> (Smap b >> Tmap b) = Smap a >> Gf >> Tmap b).
rewrite<- cat_comp_assoc.
f_equal.
apply Scommute.

assert (H1 : Smap a >> Gf >> Tmap b   = Smap a >> Tmap a >> Hf).
rewrite! cat_comp_assoc.
f_equal.
apply Tcommute.

apply (eq_trans H0 H1).
Defined.
Notation "s >>>> t" := (comp_nat_tr s t) (at level 40, left associativity). (* Moche ... *)

Lemma nat_tr_id_r {C D: Category} {F G: Functor C D} (S: Natural_Transformation F G) : S >>>> id_nat_tr G = S.
Admitted.

Lemma nat_tr_id_l {C D: Category} {F G: Functor C D} (S: Natural_Transformation F G) : id_nat_tr F >>>> S = S.
unfold id_nat_tr. destruct S. simpl.

assert (n_ob0 = fun a : ob => id (f_ob a) >> n_ob0 a).
apply functional_extensionality_dep. intro. now rewrite cat_id_l.

(* Record dependent = prise de tête
rewrite H. *)
Admitted.

Lemma nat_tr_comp_assoc {C D: Category} {F G H I: Functor C D}
    (R: Natural_Transformation F G) (S: Natural_Transformation G H) (T: Natural_Transformation H I) :
    (R >>>> S) >>>> T = R >>>> (S >>>> T).
Admitted.

Instance functor_cat (C D: Category) : Category.
apply (Build_Category (Functor C D) Natural_Transformation id_nat_tr (fun _ _ _ s t => comp_nat_tr s t)).
- intros. apply nat_tr_id_r.
- intros. apply nat_tr_id_l.
- intros. apply nat_tr_comp_assoc.
Defined.
