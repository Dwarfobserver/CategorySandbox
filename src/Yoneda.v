Require Import Category Functor Transform.
Require Import FunctionalExtensionality.

Set Universe Polymorphism.

Definition hom_ (X Y : Type) := X -> Y.
Definition id_ (X : Type) := fun x : X => x.
Definition comp_ {X Y Z : Type} (f : hom_ X Y) (g : hom_ Y Z) := fun (x : X) => g (f x).

Lemma id_r {X Y : Type} (f : hom_ X Y) : comp_ f (id_ Y) = f.
Proof.
apply functional_extensionality. intro. now unfold comp_, id_.
Qed.

Lemma id_l {X Y : Type} (f : hom_ X Y) : comp_ (id_ X) f = f.
Proof.
apply functional_extensionality. intro. now unfold comp_, id_.
Qed.

Lemma comp_assoc {X Y Z T: Type} (f : hom_ X Y) (g : hom_ Y Z) (h : hom_ Z T) : 
    comp_ (comp_ f g) h = comp_ f (comp_ g h).
Proof.
apply functional_extensionality. intro. now unfold comp_.
Qed.

Definition Ens : Category := {|
    ob := Type;
    hom := hom_;  
    
    id := id_;
    comp := @comp_ ;

    cat_id_r := @id_r;
    cat_id_l := @id_l;
    cat_comp_assoc := @comp_assoc;
|}.

Definition hom_obj {C : Category} (a : [C]) : [C] -> [Ens] := fun b => a ~> b.  
Program Definition hom_cov {C : Category} (a : [C]) : Functor C Ens := {|
    f_ob b := hom_obj a b;
    f_hom {a b: [C]} (f: a ~> b) := f_ob a ~> f_ob b ;
|}.
