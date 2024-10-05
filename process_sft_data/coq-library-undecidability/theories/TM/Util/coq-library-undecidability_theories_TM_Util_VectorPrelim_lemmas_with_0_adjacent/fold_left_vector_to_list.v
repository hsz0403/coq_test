From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.
Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X := match v with | Vector.nil _ => List.nil | Vector.cons _ x n v' => x :: vector_to_list v' end.

Lemma fold_left_vector_to_list (X Y : Type) (n : nat) (f : Y -> X -> Y) (v : Vector.t X n) (a : Y) : Vector.fold_left f a v = fold_left f (vector_to_list v) a.
Proof.
revert a.
induction v as [ | x n v IH]; intros; cbn in *; f_equal; auto.
