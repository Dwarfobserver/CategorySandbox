
Require Import Nat List Equality.
Import ListNotations.

(* +------------+
   | Catégories |
   +------------+
*)

(* Comment conserver les notations en dehors de la définition ?
   Utilise les univers polymorphiques pour permettre d'avoir une catégorie de catégories.
*)
Reserved Notation "a ~> b" (at level 90, right associativity).
Reserved Notation "f >> g" (at level 40, left associativity).

Polymorphic Class Category := {
    ob : Type ;
    hom : ob -> ob -> Type where "a ~> b" := (hom a b);
    id {a: ob} : a~>a ;
    comp {a b c: ob} : a~>b -> b~>c -> a~>c where "f >> g" := (comp f g);

    cat_id_r {a b: ob} (f: a~>b) : f  >> id = f ;
    cat_id_l {a b: ob} (f: a~>b) : id >> f  = f ;
    cat_comp_assoc {a b c d: ob} (f: a~>b) (g: b~>c) (h: c~>d) : (f >> g) >> h = f >> (g >> h) ;
}.
Notation "a ~> b" := (hom a b).
Notation "f >> g" := (comp f g).

Instance op_cat (C: Category) : Category. (* Comment pouvoir juste utiliser 'id' > *)
apply (Build_Category ob (fun a b => b ~> a) (@id _) (fun _ _ _ f g => comp g f)) ; intros.
- apply cat_id_l.
- apply cat_id_r.
- apply (eq_sym (cat_comp_assoc h g f)).
Defined.

Lemma cat_op_involutive (C: Category) : op_cat (op_cat C) = C.
unfold op_cat. destruct C. simpl. f_equal.
(*rewrite eq_sym_involutive ?*)
Admitted.

(* +-----------+
   | Foncteurs |
   +-----------+
*)

Class Functor (C D: Category) := {
    f_ob : (@ob C) -> (@ob D) ;
    f_hom {a b: @ob C} (f: a ~> b) : f_ob a ~> f_ob b ;

    f_id_distr (a: @ob C) : f_hom (@id _ a) = @id _ (f_ob a) ;
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
- intros. rewrite f_id_distr. apply f_id_distr.
- intros. rewrite f_commute. apply f_commute.
Defined.
Notation "f >>> g" := (comp_functor f g) (at level 40, left associativity).

Lemma functor_id_r {C D: Category} (F: Functor C D) : F >>> id_functor D = F.
unfold comp_functor, id_functor. destruct F. simpl. f_equal.
(* Comment simplifier ou faire disparaître les eq_ind / ed_ind_r / eq_rect ? *)
Admitted.

Lemma functor_id_l {C D: Category} (F: Functor C D) : id_functor C >>> F = F.
unfold comp_functor, id_functor. destruct F. simpl. f_equal.
Admitted.

Lemma functor_comp_assoc {A B C D: Category} (F: Functor A B) (G: Functor B C) (H: Functor C D) :
    (F >>> G) >>> H = F >>> (G >>> H).
unfold comp_functor, id_functor. simpl. f_equal.
Admitted.

Instance category_cat : Category.
apply (Build_Category Category Functor id_functor (fun _ _ _ f g => f >>> g)) ; intros.
- apply functor_id_r.
- apply functor_id_l.
- apply functor_comp_assoc.
Admitted.

(* Tentative de définition d'égalité entre 2 foncteurs *)

(* Auxiliaire gênant *)
Definition eq_functor_aux {C D: Category} {F G: Functor C D} {a b: @ob C} (f: a~>b)
    (e: forall (x: @ob C), @f_ob _ _ F x = @f_ob _ _ G x) :
    ((@f_ob _ _ F a ~> @f_ob _ _ F b) -> (@f_ob _ _ G a ~> @f_ob _ _ G b)).
rewrite e, e. trivial.
Defined.

Definition eq_functor {C D: Category} (F G: Functor C D) : Prop := 
    exists (e_ob: forall (a: @ob C), (@f_ob _ _ F a = @f_ob _ _ G a)),
    forall (a b: @ob C) (f: a~>b),
        let rw := eq_functor_aux f e_ob in
        let Ff := rw (@f_hom _ _ F _ _ f) in
        let Gf :=    (@f_hom _ _ G _ _ f) in
        Ff = Gf.

Lemma functor_id_id_eq C : eq_functor (id_functor C) (id_functor C).
unfold eq_functor, eq_functor_aux. simpl.
exists (fun (x: ob) => eq_refl x).
Admitted.

(* +----------------------------+
   | Transformations naturelles |
   +----------------------------+
*)

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
apply (Build_Natural_Transformation _ _ _ _ (fun a => n_ob a >> n_ob a (*TODO: pas la bonne fonction*))).
Admitted.

Instance functor_cat (C D: Category) : Category.
apply (Build_Category (Functor C D) Natural_Transformation id_nat_tr (fun _ _ _ s t => comp_nat_tr s t)).
Admitted.

(* +----------------------+
   | Instances canoniques |
   +----------------------+
*)

Instance discrete_cat (T: Type) : Category.
apply (Build_Category T eq (@eq_refl T) (@eq_trans T)).
- apply eq_trans_refl_r.
- apply eq_trans_refl_l.
- intros. apply (eq_sym (eq_trans_assoc f g h)).
Defined.

Lemma cat_discrete_op_id T : op_cat (discrete_cat T) = discrete_cat T.
unfold op_cat, discrete_cat. simpl. (*f_equal ?*)
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

(* Peut être utile pour définir de petites catégories,
   par exemple pour les produits/équaliseurs via limites,
   en générant la catégorie correspondant au graphe.
Record fin_graph T := {
    nodes: list T ;
    edges: list (T * T) ;
    uniqueness: NoDup nodes /\ NoDup edges ;
    closed: let (s, t) := (split edges) in incl s nodes /\ incl t nodes ;
}. *)


