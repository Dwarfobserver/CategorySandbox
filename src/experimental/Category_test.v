Reserved Notation "a ~> b" (at level 90, right associativity).
Reserved Notation "f >> g" (at level 40, left associativity).
(** The basic definition of a category *)
Polymorphic Cumulative Class Category : Type :=
{
  (** Type of Objects *)
  Obj : Type;

  (** Type of morphism beween two objects *)
  Hom : Obj -> Obj -> Type where "a ~> b" := (Hom a b);

  (** composition of morphisms: *)
  compose : forall {a b c : Obj}, (a ~> b) -> (b ~> c) -> (a ~> c)
    where "f >> g" := (compose f g);

  (** associativity of composition: *)
  assoc : forall {a b c d : Obj} (f : a ~> b) (g : b ~> c) (h : c ~> d),
            ((f >> g) >> h = f >> (g >> h));

  (** symmetric form of associativity: *)
  assoc_sym : forall {a b c d : Obj} (f : a ~> b) (g : b ~> c) (h : c ~> d),
                (f >> (g >> h) = (f >> g) >> h);

  (** identity morphisms: *)
  id : forall (a : Obj), a ~> a;

  (** id left unit: *)
  id_unit_left : forall (a b : Obj) (h : a ~> b), id a >> h = h;

  (** id right unit: *)
  id_unit_right : forall (a b : Obj) (h : a ~> b), h >> id b = h
}.

Notation "f >> g" := (compose f g).
Notation "a ~> b" := (Hom a b).

Bind Scope category_scope with Category.

Bind Scope morphism_scope with Hom.

Bind Scope object_scope with Obj.


Definition Opposite (C : Category) : Category :=
{|

  Obj := Obj;

  Hom := fun a b => (b ~> a);

  compose :=
    fun a b c (f : b ~> a) (g : c ~> b) => compose g f;

  id := fun c => id c;

  assoc := fun _ _ _ _ f g h => assoc_sym h g f;

  assoc_sym := fun _ _ _ _ f g h => assoc h g f;

  id_unit_left := fun _ _ h => @id_unit_right C _ _ h;

  id_unit_right := fun _ _ h => @id_unit_left C _ _ h

|}.

Notation "C '^op'" := (Opposite C) (at level 90, right associativity).

Generalizable All Variables.
Require Import Coq.Logic.FunctionalExtensionality.
Lemma C_op_op_eq_C (C : Category) : (C^op)^op = C.
Proof.
unfold Opposite. simpl. apply functional_extensionality_dep.
