From Undecidability Require Import TM.Util.TM_facts.
Require Import Lia.
Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X := match v with | Vector.nil _ => List.nil | Vector.cons _ x n v' => x :: vector_to_list v' end.

Lemma vector_nth_error_nat X n' i (xs : Vector.t X n') : nth_error (Vector.to_list xs) i = match lt_dec i n' with Specif.left H => Some (Vector.nth xs (Fin.of_nat_lt H)) | _ => None end.
Proof.
clear.
rewrite <- vector_to_list_correct.
induction xs in i|-*.
now destruct i.
cbn in *.
destruct i;cbn.
easy.
rewrite IHxs.
do 2 destruct lt_dec.
4:easy.
now symmetry;erewrite Fin.of_nat_ext.
all:exfalso;Lia.nia.
