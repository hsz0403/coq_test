From Undecidability Require Import MaxList.
From Undecidability Require Import TM.Util.TM_facts TM.Code.CodeTM.
From Undecidability Require Import TM.Util.VectorPrelim.
From Undecidability Require Import L.Prelim.MoreList.

Lemma max_list_rec_eq_foldl (a : nat) (xs : list nat) : fold_left max xs a = max_list_rec a xs.
Proof.
revert a.
induction xs as [ | x xs IH]; intros; cbn in *.
-
reflexivity.
-
rewrite IH.
rewrite !max_list_rec_max.
nia.
