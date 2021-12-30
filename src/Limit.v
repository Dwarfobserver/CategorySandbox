Require Import Category Functor Transform.
Require Import Coq.Setoids.Setoid.

Definition universal_arrow {C : Category} (a b : [C]) := 
    exists f : a ~> b, forall g : a ~> b, f = g.

Notation "a ---> b" := (universal_arrow a b) (at level 90, right associativity).

Definition is_initial {C : Category} (x : [C]) := 
    forall y : [C], x ---> y.

Definition is_terminal {C : Category} (x : [C]) := 
    forall y : [C], y ---> x.

Lemma terminal_iff_initial_op {C : Category} (x : [C]) : 
    is_terminal x <-> @is_initial (C^op) x .
Proof.
split; unfold is_initial, is_terminal;
intros; specialize (H y); destruct H as [f]; exists f; assumption.
Qed.

Lemma initial_iff_terminal_op  {C : Category} (x : [C]) : 
    is_initial x <-> @is_terminal (C^op) x.
Proof.
rewrite terminal_iff_initial_op. reflexivity.
Qed.


Lemma initials_are_isom {C : Category} (a b : [C]) :
    is_initial a -> is_initial b -> a ≃ b.
Proof.
intros. unfold is_initial in *.
assert (a ---> a). apply H.
assert (b ---> b). apply H0.
specialize (H b). specialize (H0 a). 
destruct H as [f], H0 as [f'], H1 as [fa], H2 as [fb]. exists f. unfold is_iso. exists f'. split.
- assert (fa = id a). apply H1. rewrite <- H3. apply eq_sym, H1.
- assert (fb = id b). apply H2. rewrite <- H2. apply eq_sym, H2.
Qed.

Lemma terminals_are_isom {C : Category} (a b : [C]) :
    is_terminal a -> is_terminal b -> a ≃ b.
Proof.
rewrite !terminal_iff_initial_op. intros. rewrite <- op_isom_iff_isom. now apply initials_are_isom.
Qed.

