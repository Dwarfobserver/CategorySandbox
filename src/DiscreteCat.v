Require Import Category Functor Transform Comma Limit.
Require Import Equality ProofIrrelevance.

Module Discrete.

(* Wo, Program Definition does everything by itself... *)
Program Definition Cat : Category := {|
    ob := nat;
    hom := fun x y => x = y;
|}.

Definition diagram_hom {C : Category} {x y : [Cat]} (F : [Cat] -> [C]) (f : x ~> y) : (F x) ~> (F y).
rewrite f. exact (id (F y)).
Defined.

Program Definition construct_diagram {C : Category} (F : [Cat] -> [C]) : Cat → C := {|
    f_ob := F;
    f_hom := fun _ b _ => id (F b);
|}.
Next Obligation.
simpl. now rewrite cat_id_l.
Defined.
    
End Discrete.

Module fDiscrete.

Fixpoint Ob (n : nat) :=
    match n with
    | 0 => True
    | S n => ((Ob n) * True)%type
    end.

Definition Hom (n : nat) (a b : Ob n) := a = b. 

Program Definition Cat (n : nat) : Category := {|
    ob := Ob n;
    hom := Hom n;
    id a := eq_refl a;
|}.
Next Obligation.
now rewrite H.
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

End fDiscrete.
