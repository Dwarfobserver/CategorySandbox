
Require Import Nat List MSets.
Import ListNotations.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix ">>" (at level 40, left associativity).

(* Comment conserver les notations en dehors de la définition ?
   utilse les univers polymorphiques pour permettre d'avoir une catégorie de catégories.
*)
Polymorphic Class Category := {
    ob   : Type;
    hom  : ob -> ob -> Type where "a ~> b" := (hom a b) ;
    id   {a: ob} : a~>a;
    comp {a b c: ob} : a~>b -> b~>c -> a~>c
                where "f >> g" := (comp f g) ;

    id_r {a b: ob} (f: a~>b) : f  >> id = f ;
    id_l {a b: ob} (f: a~>b) : id >> f  = f ;
    assoc {a b c d: ob} (f: a~>b) (g: b~>c) (h: c~>d) :
        (f >> g) >> h = f >> (g >> h) ;
}.

Instance discrete_cat (T: Type) : Category.
apply (Build_Category T eq (@eq_refl T) (@eq_trans T)).
- apply eq_trans_refl_r.
- apply eq_trans_refl_l.
- intros. apply (eq_sym (eq_trans_assoc f g h)).
Defined.

(* Les notations me manquent ... *)
Class Functor (C D: Category) := {
    f_ob : (@ob C) -> (@ob D) ;
    f_hom {a b: @ob C} (f: @hom C a b) : @hom D (f_ob a) (f_ob b) ;
    f_commute {a b c: @ob C} (f: @hom C a b) (g: @hom C b c) :
        f_hom (comp f g) = comp (f_hom f) (f_hom g) ;
}.

Instance discrete_functor {A B} (f: A -> B) : Functor (discrete_cat A) (discrete_cat B).
apply (Build_Functor (discrete_cat A) (discrete_cat B) f (f_equal f)).
simpl. intros. apply eq_trans_map_distr.
Defined.

Instance constant_functor (C D: Category) (d: @ob D) : Functor C D.
apply (Build_Functor C D (fun _ => d) (fun _ _ _ => @id _ d)).
intros. apply (eq_sym (id_r (@id _ d))).
Defined.

Instance id_functor (C: Category) : Functor C C.
apply (Build_Functor C C (fun x => x) (fun _ _ f => f)).
reflexivity.
Defined.

Definition comp_functor {C D E: Category} (F: Functor C D) (G: Functor D E) : Functor C E.
apply (Build_Functor C E (fun c => f_ob (f_ob c)) (fun _ _ f => f_hom (f_hom f))).
intros. rewrite<- f_commute. apply f_equal. rewrite f_commute. reflexivity.
Defined.

Polymorphic Instance category_cat : Category.
apply (Build_Category Category Functor id_functor (fun _ _ _ f g => comp_functor f g))
    ; unfold id_functor ; unfold comp_functor ; simpl.
- admit.
- admit.
- admit.
Admitted.

(* Dégueu *)
Class Natural_Transformation {C D: Category} (F G: Functor C D) := {
    n_ob (a b: @ob D) : @hom D a b;
    n_commute {a b: @ob C} (f: @hom C a b) :
        let Na := (n_ob (@f_ob _ _ F a) (@f_ob _ _ G a)) in
        let Nb := (n_ob (@f_ob _ _ F b) (@f_ob _ _ G b)) in
        let Ff := (@f_hom _ _ F _ _ f) in
        let Gf := (@f_hom _ _ G _ _ f) in
        comp Ff Nb = comp Na Gf ;
}.

(* Peut être utile pour définir de petites catégories,
   par exemple pour les produits/équaliseurs via limites,
   en générant la catégorie correspondant au graphe.
Record fin_graph T := {
    nodes: list T ;
    edges: list (T * T) ;
    uniqueness: NoDup nodes /\ NoDup edges ;
    closed: let (s, t) := (split edges) in incl s nodes /\ incl t nodes ;
}. *)


