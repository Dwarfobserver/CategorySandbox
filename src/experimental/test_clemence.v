Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix ">>" (at level 40, left associativity).

Polymorphic Class Category := {
    ob   : Type ;
    hom  : ob -> ob -> Type where "a ~> b" := (hom a b);
    id   {a: ob} : a~>a;
    comp {a b c: ob} : a~>b -> b~>c -> a~>c
                where "f >> g" := (comp f g) ;

    id_r {a b: ob} (f: a~>b) : f  >> id = f ;
    id_l {a b: ob} (f: a~>b) : id >> f  = f ;
    assoc {a b c d: ob} (f: a~>b) (g: b~>c) (h: c~>d) :
        (f >> g) >> h = f >> (g >> h) ;
}.
Notation "a ~> b" := (hom a b).
Notation "f >> g" := (comp f g).

Instance discrete_cat (T: Type) : Category.
apply (Build_Category T eq (@eq_refl T) (@eq_trans T)).
- apply eq_trans_refl_r.
- apply eq_trans_refl_l.
- intros. apply (eq_sym (eq_trans_assoc f g h)).
Defined.

Class Functor (C D: Category) := {
    f_ob : (@ob C) -> (@ob D) ;
    f_hom {a b: @ob C} (f: a ~> b) : f_ob a ~> f_ob b ;

    f_id (a: @ob C) : f_hom (@id _ a) = @id _ (f_ob a) ;
    f_commute {a b c: @ob C} (f: a ~> b) (g: b ~> c) :
        f_hom (f >> g) = (f_hom f) >> (f_hom g) ;
}.

Definition comp_functor {A B C : Category} (F : Functor A B) (G : Functor B C) : Functor A C.
    apply (Build_Functor A C (fun a => f_ob (f_ob a)) (fun _ _ f => f_hom (f_hom f))).
    - intros. now rewrite !f_id.
    - intros. now rewrite !f_commute.
Defined.

Definition equiv_functor {A B : Category} (F G : Functor A B) :=
    forall a, @f_ob A B F a = @f_ob A B G a 
    (* /\ @f_hom A B G = @f_hom A B F does not compile *).

Notation "F ≡ G" := (equiv_functor F G) (at level 40, left associativity).

Instance id_functor (C : Category) : Functor C C.
    apply (Build_Functor C C (fun x => x) (fun _ _ f => f)); reflexivity.
Defined.

Notation "F >>> G" := (comp_functor F G) (at level 40, left associativity).

Lemma functor_id_left (A B : Category) (F : Functor A A) : (F) >>> F ≡ F.
Proof.
Admitted.
    



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


Instance TWO : Category.
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
        Admitted.
        
        
         
    

End DIS.



