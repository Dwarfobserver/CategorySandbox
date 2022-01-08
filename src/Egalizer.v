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

Inductive Empty : Set :=.
Inductive One : Set := ID.
Inductive Two : Set := UP | DOWN.

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
destruct a, b; simpl; now destruct f.
Defined.
Next Obligation.
destruct a, b; now simpl.
Defined.
Next Obligation.
destruct a, b, c, d, f, g, h; now simpl.
Defined.

Definition diagram_ob {C : Category} (a b : [C]) (x : Obj) : [C] := 
    match x with
    | X => a
    | Y => b
    end.

Definition diagram_hom {C : Category} {a b : [C]} (f g : a ~> b) (x y : Obj) (t : Hom x y) := 
    match x, y, t return diagram_ob a b x ~> diagram_ob a b y with
    | X, X, _    => id a
    | Y, Y, _    => id b
    | X, Y, UP   => f
    | X, Y, DOWN => g
    | _, _, t    => match t with end
    end.

Program Definition construct_diagram {C : Category} {a b : [C]} (f g : a ~> b) : Cat → C := {|
    f_ob := diagram_ob a b;
    f_hom := diagram_hom f g
|}.
Next Obligation.
destruct a0; now simpl.
Defined.
Next Obligation.
destruct a0, b0, c; simpl; try rewrite cat_id_l; try rewrite cat_id_r; now simpl.
Defined.

End Egalizer