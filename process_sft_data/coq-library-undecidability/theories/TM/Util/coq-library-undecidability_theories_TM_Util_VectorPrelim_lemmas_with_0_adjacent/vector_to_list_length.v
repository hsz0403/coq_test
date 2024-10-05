From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.
Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X := match v with | Vector.nil _ => List.nil | Vector.cons _ x n v' => x :: vector_to_list v' end.

Lemma vector_to_list_length (X : Type) (n : nat) (v : Vector.t X n) : length (vector_to_list v) = n.
Proof.
induction v.
-
cbn.
auto.
-
cbn.
f_equal.
auto.
