From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.
Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X := match v with | Vector.nil _ => List.nil | Vector.cons _ x n v' => x :: vector_to_list v' end.

Lemma list_eq_nth_error X (xs ys : list X) : (forall n, nth_error xs n = nth_error ys n) -> xs = ys.
Proof.
induction xs in ys|-*;destruct ys;cbn;intros H.
1:easy.
1-2:now specialize (H 0).
generalize (H 0).
intros [= ->].
erewrite IHxs.
easy.
intros n'.
now specialize (H (S n')).
