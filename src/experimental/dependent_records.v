
Require Import Category Functor FunctionalExtensionality Program.Equality.

(* This file aims to experiment & simplify proofs about equality of dependent records *)

Fixpoint valid (n: nat) : bool :=
  match n with
    | 0 => true
    | 1 => false
    | S (S p) => valid p
  end.

Record valid_nat : Type :=
  { VN_value : nat ;
    VN_prop  : valid VN_value = true }.

Definition transport {A : Type} (B : A -> Type) {a b : A}: a = b -> B a -> B b.
Proof.
  intros [] ?; assumption.
Defined.

Lemma valid_nat_unique (m n : valid_nat) (p : VN_value m = VN_value n):
  transport (fun k => valid k = true) p (VN_prop m) = VN_prop n ->
  m = n.
Proof.
  destruct m; destruct n.
  simpl in * |- *.
  destruct p.
  intros [].
  reflexivity.
Qed.

(* Pre-cat *)

Definition transport_hom o := o->o->Type.

Record Cat_ObHom := {
  c1_ob : Type;
  c1_hom : transport_hom c1_ob;
}.

Lemma eq_cat_oh (c1 c2: Cat_ObHom)
  (e_ob:  c1_ob c1 = c1_ob c2)
  (e_hom: transport transport_hom e_ob (c1_hom c1) = c1_hom c2)
  : c1 = c2.
destruct c1, c2. simpl in *.
now destruct e_ob, e_hom.
Qed.

Definition transport_id oh := forall (a: c1_ob oh), (c1_hom oh) a a.
Definition transport_comp oh := forall (a b c: c1_ob oh), (c1_hom oh) a b -> (c1_hom oh) b c -> (c1_hom oh) a c.

Record Cat_Data := {
  c2_oh : Cat_ObHom;
  c2_id : transport_id c2_oh;
  c2_comp : transport_comp c2_oh;
}.

Lemma eq_cat_data (d1 d2: Cat_Data)
  (e_oh: c2_oh d1 = c2_oh d2)
  (e_id: transport transport_id e_oh (c2_id d1) = c2_id d2)
  (e_comp: transport transport_comp e_oh (c2_comp d1) = c2_comp d2)
  : d1 = d2.
destruct d1, d2. simpl in *.
now destruct e_oh, e_id, e_comp.
Qed.

Definition cat_oh_of (C: Category) := Build_Cat_ObHom ob hom.
Definition cat_data_of (C: Category) := Build_Cat_Data (cat_oh_of C) id (@comp C).

Lemma eq_category (C D: Category) (e: cat_data_of C = cat_data_of D) : C = D.
set (c := cat_data_of C).
set (d := cat_data_of D).
(* assert (e_cd := e).
change (cat_data_of C) with c in e_cd ; change (cat_data_of D) with d in e_cd. *)
destruct C, D.

unfold cat_data_of, cat_oh_of in c, d, e.
simpl in *.

assert (e_ob : ob = ob0).
now dependent destruction e.
destruct e_ob.

assert (e_hom : hom = hom0).
now dependent destruction e.
destruct e_hom.

assert (e_id : id = id0).
assert (e_idc : id = c2_id c). reflexivity.
assert (e_idd : id0 = c2_id d). reflexivity.
dependent destruction e.
admit.
destruct e_id.

assert (e_comp : comp = comp0).
admit.
destruct e_comp.

(* Is transporting proofs possible ? Otherwise use UIP *)
assert (e_id_r : cat_id_r = cat_id_r0).
admit.
destruct e_id_r.

assert (e_id_l : cat_id_l = cat_id_l0).
admit.
destruct e_id_l.

assert (e_assoc : cat_comp_assoc = cat_comp_assoc0).
admit.
destruct e_assoc.

reflexivity.
Admitted.
