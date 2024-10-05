From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.
Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X := match v with | Vector.nil _ => List.nil | Vector.cons _ x n v' => x :: vector_to_list v' end.

Lemma vector_to_list_cast (X : Type) (n1 n2 : nat) (H : n1 = n2) (v : Vector.t X n1) : vector_to_list (Vector.cast v H) = vector_to_list v.
Proof.
subst.
rename n2 into n.
induction v as [ | x n v IH]; cbn; f_equal; auto.
