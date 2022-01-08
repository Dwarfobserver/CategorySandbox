Require Import Category Functor Transform Comma Limit.
Require Import Equality ProofIrrelevance.


Module Egalizer.

(*
    Egalizer diagram :
        UP
       ------->
    X           Y
       ------->
        DOWN
*)

Inductive Obj := X | Y.

Inductive Empty : Prop :=.
Inductive One : Prop := ID.
Inductive Two : Prop := UP | DOWN.

Definition Hom (x y : Obj) := 
    match x, y with
    | X, X => One
    | Y, Y => One
    | X, Y => Two
    | Y, X => Empty
    end.

Definition Id (x : Obj) : Hom x x.
destruct x; now simpl.
Defined.

Program Definition Cat : Category := {|
    ob := Obj;
    hom := Hom;
    id  := Id;
|}.
Next Obligation.
destruct a, b, c; now simpl.
Defined.
Next Obligation.
apply proof_irrelevance.
Defined.
Next Obligation.
apply proof_irrelevance.
Defined.
Next Obligation.
apply proof_irrelevance.
Defined.

Definition diagram_ob {C : Category} (a b : [C]) (x : Obj) : [C] := 
    match x with
    | X => a
    | Y => b
    end.

(* This works but it's not quite what we want. There is a univser problem *)
Definition diagram_hom {C : Category} {a b : [C]} (f g : a ~> b) (x y : Obj) := 
    match x, y return Hom x y -> diagram_ob a b x ~> diagram_ob a b y with
    | X, X => fun t : Hom X X => id a
    | Y, Y => fun t : Hom Y Y => id b
    | X, Y => fun t : Hom X Y => f
    | Y, X => fun t : Hom Y X => match t with end
    end.

Definition diagram_hom {C : Category} {a b : [C]} (f g : a ~> b) (x y : Obj) := 
    match x, y return Hom x y -> diagram_ob a b x ~> diagram_ob a b y with
    | X, X => fun t : Hom X X => id a
    | Y, Y => fun t : Hom Y Y => id b
    | X, Y => fun t : Hom X Y => match t with
                                 | UP => f
                                 | DOWN => g
                                 end
    | Y, X => fun t : Hom Y X => match t with end
    end.



(*
Definition diagram_hom {C : Category} {a b : [C]} (f g : a ~> b) (x y : Obj) (t : Hom x y) :
     diagram_ob a b x ~> diagram_ob a b y := 
    match x, y, t with
    | X, Y, UP => f
    | X, Y, DOWN => g
    | Y, Y, ID => id b
    | X, X, ID => id a
    | _, _, t => match t with end
    end.

*)