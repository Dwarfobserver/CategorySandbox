
Require Import Nat List Equality FunctionalExtensionality.
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
    ob : Type;
    hom : ob -> ob -> Type where "a ~> b" := (hom a b);
    id (a: ob) : a~>a;
    comp {a b c: ob} : a~>b -> b~>c -> a~>c where "f >> g" := (comp f g);

    cat_id_r {a b: ob} (f: a~>b) : f >> (id b) = f;
    cat_id_l {a b: ob} (f: a~>b) : (id a) >> f = f;
    cat_comp_assoc {a b c d: ob} (f: a~>b) (g: b~>c) (h: c~>d) : (f >> g) >> h = f >> (g >> h);
}.
Notation "a ~> b" := (hom a b).
Notation "f >> g" := (comp f g).

Instance op_cat (C: Category) : Category. (* Comment pouvoir juste utiliser 'id' > *)
apply (Build_Category ob (fun a b => b ~> a) id (fun _ _ _ f g => comp g f)) ; intros.
- apply cat_id_l.
- apply cat_id_r.
- apply (eq_sym (cat_comp_assoc h g f)).
Defined.

Lemma cat_op_involutive (C: Category) : op_cat (op_cat C) = C.
unfold op_cat. destruct C. simpl. f_equal.
repeat (apply functional_extensionality_dep ; intro).
apply eq_sym_involutive.
Qed.

(* +-----------+
   | Foncteurs |
   +-----------+
*)

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
(* Possible de complètement éviter les réécritures pour définir les éléments ? *)
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

Instance category_cat : Category.
apply (Build_Category Category Functor id_functor (fun _ _ _ f g => f >>> g)) ; intros.
- apply functor_id_r.
- apply functor_id_l.
- apply functor_comp_assoc.
Defined.

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
destruct S as [Smap Scommute], T as [Tmap Tcommute].
apply (Build_Natural_Transformation _ _ _ _ (fun a => (Smap a) >> (Tmap a))).
intros. rename Gf into Hf.
set (Gf := @f_hom _ _ G _ _ f).

(* Prouve la naturalité en passant par le chemin du milieu. *)

(* Pourquoi les rewrite ne fonctionnenet plus avec une variable (comme p_half) ?
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
unfold op_cat, discrete_cat. simpl. rewrite eq_sym.
f_equal (* Record dependent mais il n'existe pas de f_equal dependent *).
Admitted.

(*
Record Category_Data := {
    data_ob : Type;
    data_hom : data_ob -> data_ob -> Type;
    data_id {a: data_ob} : data_hom a a;
    data_comp {a b c: data_ob} : (data_hom a b) -> (data_hom b c) -> (data_hom a c);
}.
Definition get_data (C: Category) := Build_Category_Data ob hom id (fun _ _ _ f g => f >> g).

Definition transport {A: Type} (P: A -> Type) {x y: A} :
    x = y -> P x -> P y.
intros []. trivial.
Defined.
Definition transport1 {A B: Type} (P: forall (x:A), B -> Type) {x y: A} :
    x = y -> (forall b, P x b -> P y b).
intros []. trivial.
Defined.
Definition transport2 {A B C: Type} (P: A -> B -> C -> Type) {x y: A} :
    x = y -> (forall b c, P x b c -> P y b c).
intros []. trivial.
Defined.

Definition Transport_Category (C D: Category) : (get_data C = get_data D) -> C = D.
unfold get_data. intro e. destruct C, D. rewrite ().
Defined.
*)

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


