Require Import Egality.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix ">>" (at level 40, left associativity).

Polymorphic Class Category := {
    ob   : Type ;
    hom  : ob -> ob -> Type where "a ~> b" := (hom a b);
    id   {a: ob} : a ~> a;
    comp {a b c: ob} : a~>b -> b~>c -> a~>c
                where "f >> g" := (comp f g) ;

    id_r {a b: ob} (f: a~>b) : f >> id ≃ f ;
    id_l {a b: ob} (f: a~>b) : id >> f  = f ;
    assoc {a b c d: ob} (f: a~>b) (g: b~>c) (h: c~>d) :
        (f >> g) >> h = f >> (g >> h) ;
}.