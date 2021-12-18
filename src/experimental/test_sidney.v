
Require Import Category Functor.

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
unfold op_cat, discrete_cat. simpl.
(* Record dependent *)
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


