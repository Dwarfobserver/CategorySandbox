
Reserved Notation "A ~> B" (at level 60).
Reserved Notation "f >> g" (at level 60).

Class Category
        (Ob: Type)
        (Hom: Ob -> Ob -> Type)
:= {
    ob   := Ob ;
    hom  := Hom where "a ~> b" := (Hom a b) ;
    id   {a: Ob} : a~>a;
    comp {a b c: Ob} : a~>b -> b~>c -> a~>c
                where "f >> g" := (comp f g) ;

    id_r {a b: Ob} (f: a~>b) : f  >> id = f ;
    id_l {a b: Ob} (f: a~>b) : id >> f  = f ;
    assoc {a b c d: Ob} (f: a~>b) (g: b~>c) (h: c~>d) :
        (f >> g) >> h = f >> (g >> h) ;
}.

(* Ne fonctionne que sans import (?) *)
(* Autrement apply (Build_Category id comp) j'imagine *)
Program Instance discrete_cat : Category nat eq.

(* L'identité ne doit pas être opaque.
   Doit être spécifiée car ne va pas de soi :
   Pourquoi pas un "espace métrique" avec Hom: Ob -> Ob -> R+ U {+∞}, id = 0 et comp x y = x+y ?
   Mérite peut-être de paramétriser Category avec comp ...
*)
Next Obligation.
intros.
exact eq_refl.
Defined.

(* Pareil pour la composition. *)
Next Obligation.
simpl in *.
etransitivity.
exact H.
exact H0.
Defined.

Next Obligation.
unfold discrete_cat_obligation_1, discrete_cat_obligation_2.
apply eq_trans_refl_r.
Qed.

Next Obligation.
unfold discrete_cat_obligation_1, discrete_cat_obligation_2.
apply eq_trans_refl_l.
Qed.

Next Obligation.
unfold discrete_cat_obligation_1.
intros.
apply (eq_sym (eq_trans_assoc f g h)).
Qed.

Print discrete_cat.
