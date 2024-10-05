Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import folProp.
Require Import folProof.
Require Import subProp.
Require Import folLogic3.
Require Import folReplace.
Require Import NN.
Require Import PAtheory.
Require Export LNN2LNT.
Require Import subAll.
Require Import ListExt.

Lemma NN2PA : forall f : fol.Formula LNN, folProof.SysPrf LNN NN f -> SysPrf PA (LNN2LNT_formula f).
Proof.
intros.
apply translateProof with NN.
apply closedPA1.
intros.
unfold NN in H0.
induction H0 as [x H0| x H0].
induction H0 as [x H0| x H0].
induction H0 as [x H0| x H0].
induction H0 as [x H0| x H0].
induction H0 as [x H0| x H0].
induction H0 as [x H0| x H0].
induction H0 as [x H0| x H0].
induction H0 as [x H0| x H0].
induction H0.
apply Axm; repeat (try right; constructor) || left.
induction H0.
apply Axm; repeat (try right; constructor) || left.
induction H0.
apply Axm; repeat (try right; constructor) || left.
induction H0.
apply Axm; repeat (try right; constructor) || left.
induction H0.
apply Axm; repeat (try right; constructor) || left.
induction H0.
apply Axm; repeat (try right; constructor) || left.
induction H0.
apply NN72PA.
induction H0.
apply NN82PA.
induction H0.
apply NN92PA.
apply H.
