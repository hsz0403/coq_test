Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import subAll.
Require Import folReplace.
Require Import folProp.
Require Import folLogic3.
Require Import NN.
Require Import LNN2LNT.
Require Export PA.

Lemma NN82PA : SysPrf PA (LNN2LNT_formula NN8).
Proof.
replace (LNN2LNT_formula NN8) with (forallH 1 (forallH 0 (impH (LNN2LNT_formula (LNN.LT (LNN.var 0) (LNN.Succ (LNN.var 1)))) (orH (LNN2LNT_formula (LNN.LT (LNN.var 0) (LNN.var 1))) (equal (var 0) (var 1)))))).
simpl in |- *.
repeat rewrite translateLT1.
simpl in |- *.
unfold newVar in |- *.
simpl in |- *.
fold var in |- *.
fold (Succ (var 3)) in |- *.
fold (Succ (var 1)) in |- *.
fold (Plus (var 0) (Succ (var 3))) in |- *.
fold equal in |- *.
fold (fol.existH LNT 3 (equal (Plus (var 0) (Succ (var 3))) (Succ (var 1)))) in |- *.
fold (fol.existH LNT 3 (equal (Plus (var 0) (Succ (var 3))) (var 1))) in |- *.
fold existH in |- *.
apply forallI.
apply closedPA.
apply forallI.
apply closedPA.
apply impI.
apply existSys.
apply closedPA.
simpl in |- *.
unfold not in |- *; intros.
repeat (elim H; clear H; [ discriminate | intros ]); auto.
eapply orE.
apply sysWeaken.
apply paZeroOrSucc.
apply impI.
apply orI2.
apply impE with (equal (Succ (var 0)) (Succ (var 1))).
repeat simple apply sysWeaken.
apply pa2.
apply eqTrans with (Plus (var 0) (Succ (var 3))).
apply eqTrans with (Succ (Plus (var 0) (var 3))).
apply eqSucc.
apply eqTrans with (Plus (var 0) Zero).
apply eqSym.
repeat simple apply sysWeaken.
apply pa3.
apply eqPlus.
apply eqRefl.
apply eqSym.
apply Axm; right; constructor.
apply eqSym.
repeat simple apply sysWeaken.
apply pa4.
apply Axm; left; right; constructor.
unfold newVar in |- *.
simpl in |- *.
apply impI.
apply existSys.
unfold not in |- *; intros.
induction H as (x, H); induction H as (H, H0).
induction H0 as [x H0| x H0].
elim closedPA with 4.
exists x.
auto.
induction H0.
simpl in H.
repeat (elim H; clear H; [ discriminate | intros ]); auto.
unfold not in |- *; intros.
simpl in H.
repeat (elim H; clear H; [ discriminate | intros ]); auto.
apply orI1.
apply existI with (var 4).
rewrite (subFormulaEqual LNT).
simpl in |- *.
apply impE with (equal (Succ (Plus (var 0) (Succ (var 4)))) (Succ (var 1))).
repeat simple apply sysWeaken.
apply pa2.
apply eqTrans with (Plus (var 0) (Succ (var 3))).
apply eqTrans with (Plus (var 0) (Succ (Succ (var 4)))).
repeat simple apply sysWeaken.
apply eqSym.
apply pa4.
apply eqPlus.
apply eqRefl.
apply eqSucc.
apply eqSym.
apply Axm; right; constructor.
apply Axm; left; right; constructor.
reflexivity.
