From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.
Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X := match v with | Vector.nil _ => List.nil | Vector.cons _ x n v' => x :: vector_to_list v' end.

Lemma vector_app_to_list X k k' (xs : Vector.t X k) (ys : Vector.t X k'): vector_to_list (Vector.append xs ys) = vector_to_list xs ++ vector_to_list ys.
Proof.
induction xs.
easy.
cbn.
congruence.
