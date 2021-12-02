
(* Ressemblance à un inf-groupoid ? *)
Inductive cat_eq2 : forall {A B: Type}, A -> B -> Prop :=
    (* type -1 *)
    | eq2 {A: Type} {x y: A} : x = y -> cat_eq2 x y
    (* "set" def. par les choix possibles de fonctions
       équipé de 2 égalités (avec potentiellement un contenu, d'autres fonctions)
    *)
    | iso2 {A B} : (exists (f: A->B) (g: B->A),
        (cat_eq2 (fun (a: A) => g (f a)) (fun (a: A) => a)
      /\ cat_eq2 (fun (b: B) => f (g b)) (fun (b: B) => b))
        ) -> cat_eq2 A B
.

Inductive Bool1 := T1 | F1.
Inductive Bool2 := T2 | F2.

Definition A_1_to_2 b := match b with T1 => T2 | F1 => F2 end.
Definition A_2_to_1 b := match b with T2 => T1 | F2 => F1 end.

Definition B_1_to_2 b := match b with T1 => F2 | F1 => T2 end.
Definition B_2_to_1 b := match b with T2 => F1 | F2 => T1 end.

Definition fst_eq : cat_eq2 A_1_to_2 A_2_to_1.
Admitted.

Definition snd_eq : cat_eq2 B_1_to_2 B_2_to_1.
Admitted.

Definition A_inv b := A_2_to_1 (A_1_to_2 b).
Definition B_inv b := B_2_to_1 (B_1_to_2 b).

Definition ff_ss b : cat_eq2 (A_inv b) (B_inv b).
Admitted.

Definition inv_1 b := match b with T1 => F1 | F1 => T1 end.

Definition fst_snd b : cat_eq2 (inv_1 b) (B_2_to_1 (A_1_to_2 b)).
Admitted.
