Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix ">>" (at level 40, left associativity).

Class Category
        (Ob: Type)
        (Hom: Ob -> Ob -> Type)
:= {
    ob   := Ob ;
    hom  := Hom where "a ~> b" := (Hom a b) ;
    id   {a: Ob} : a~>a;
    comp {a b c: Ob} : a~>b -> b~>c -> a~>c
                where "f >> g" := (comp f g) ;

    id_r {a b: Ob} (f: a~>b) : f  >> id = f ;
    id_l {a b: Ob} (f: a~>b) : id >> f  = f ;
    assoc {a b c d: Ob} (f: a~>b) (g: b~>c) (h: c~>d) :
        (f >> g) >> h = f >> (g >> h) ;
}.

Module TWO.

    Inductive obj := ZERO | ONE.

    Definition hom (x y : obj) := 
        match x, y with
        | ZERO, ZERO => True
        | ONE, ONE => True
        | _, _ => False 
        end.

    Definition id (x : obj) : hom x x.
        Proof.
        case x; simpl; exact I.
        Defined.


    Definition comp (x y z : obj) (f : hom x y) (g : hom y z) : hom x z.
        Proof.
        case x, z, y; simpl; try exact I; try exact g; try exact f.
        Defined.

End TWO.


Instance TWO : Category TWO.obj TWO.hom.
    Proof.
    apply (Build_Category TWO.obj TWO.hom TWO.id TWO.comp).
    - intros. case a, b; simpl in *; try case f; try reflexivity.
    - intros. case a, b; simpl in *; try case f; try reflexivity.
    - intros. case a, b, c, d, f, g, h; now simpl.
    Defined.


Module DIS.

    Definition obj := nat.

    Fixpoint hom (x y : obj) := 
        match x, y with
        | 0, 0 => True
        | 0, S n => False
        | S n, 0 => False
        | S n, S m => hom n m
        end.

    Definition id (x : obj) : hom x x.
        Proof.
        induction x.
        - reflexivity.
        - now simpl.
        Defined.
    
    Definition comp : forall x y z, hom x y -> hom y z -> hom x z.
        Proof.
        
        
         
    

End DIS.



