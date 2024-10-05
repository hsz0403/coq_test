From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.
Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X := match v with | Vector.nil _ => List.nil | Vector.cons _ x n v' => x :: vector_to_list v' end.

Lemma vector_nth_error_fin X n' i (xs : Vector.t X n') : nth_error (Vector.to_list xs) (proj1_sig (Fin.to_nat i)) = Some (Vector.nth xs i).
Proof.
clear.
rewrite <- vector_to_list_correct.
induction xs in i|-*.
now inv i.
cbn;rewrite vector_to_list_correct in *.
cbn in *.
edestruct (fin_destruct_S) as [ (i'&->)| -> ].
2:now cbn.
unshelve erewrite (_ : Fin.FS = Fin.R 1).
reflexivity.
setoid_rewrite (Fin.R_sanity 1 i').
cbn.
easy.
