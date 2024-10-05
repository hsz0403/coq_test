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

Lemma paPlusSym : forall a b : Term, SysPrf PA (equal (Plus a b) (Plus b a)).
Proof.
assert (SysPrf PA (forallH 1 (forallH 0 (equal (Plus (var 0) (var 1)) (Plus (var 1) (var 0)))))).
apply induct.
rewrite (subFormulaForall LNT).
induction (eq_nat_dec 0 1).
discriminate a.
induction (In_dec eq_nat_dec 0 (freeVarTerm LNT Zero)).
elim a.
apply induct.
repeat rewrite (subFormulaEqual LNT).
simpl in |- *.
apply eqRefl.
apply forallI.
apply closedPA.
repeat rewrite (subFormulaEqual LNT).
simpl in |- *.
apply impI.
apply eqTrans with (Succ (var 0)).
apply sysWeaken.
apply pa3 with (a := Succ (var 0)).
apply eqTrans with (Succ (Plus Zero (var 0))).
apply eqSucc.
apply eqTrans with (Plus (var 0) Zero).
apply sysWeaken.
apply eqSym.
apply pa3.
apply Axm; right; constructor.
apply eqSym.
apply sysWeaken.
apply pa4 with (a := Zero) (b := var 0).
apply forallI.
apply closedPA.
apply impI.
rewrite (subFormulaForall LNT).
induction (eq_nat_dec 0 1).
discriminate a.
induction (In_dec eq_nat_dec 0 (freeVarTerm LNT (Succ (var 1)))).
simpl in a.
induction a as [H| H].
elim b; auto.
contradiction.
rewrite (subFormulaEqual LNT).
simpl in |- *.
apply forallI.
unfold not in |- *; intros.
induction H as (x, H); induction H as (H, H0).
induction H0 as [x H0| x H0].
elim closedPA with 0.
exists x.
auto.
induction H0.
simpl in H.
decompose sum H.
discriminate H0.
discriminate H1.
apply eqTrans with (Succ (Plus (var 0) (var 1))).
apply sysWeaken.
apply pa4 with (a := var 0) (b := var 1).
apply eqTrans with (Succ (Plus (var 1) (var 0))).
apply eqSucc.
apply forallSimp with 0.
apply Axm; right; constructor.
apply sysWeaken.
apply forallSimp with 0.
apply induct.
rewrite (subFormulaEqual LNT).
simpl in |- *.
apply eqTrans with (Succ (var 1)).
fold (Succ (apply LNT Languages.Plus (Tcons LNT 1 (fol.var LNT 1) (Tcons LNT 0 Zero (Tnil LNT))))) in |- *.
apply eqSucc.
apply pa3 with (a := var 1).
apply eqSym.
apply pa3 with (a := Succ (var 1)).
apply forallI.
apply closedPA.
apply impI.
rewrite (subFormulaEqual LNT).
simpl in |- *.
apply eqTrans with (Succ (Plus (Succ (var 1)) (var 0))).
fold (Succ (apply LNT Languages.Plus (Tcons LNT 1 (fol.var LNT 1) (Tcons LNT 0 (Succ (var 0)) (Tnil LNT))))) in |- *.
apply eqSucc.
apply eqTrans with (Succ (Plus (var 1) (var 0))).
apply sysWeaken.
apply pa4 with (a := var 1) (b := var 0).
apply Axm; right; constructor.
apply sysWeaken.
apply eqSym.
apply pa4 with (a := Succ (var 1)) (b := var 0).
intros.
set (m := fun x : nat => match x with | O => a | S _ => b end) in *.
replace (equal (Plus a b) (Plus b a)) with (subAllFormula LNT (equal (Plus (var 0) (var 1)) (Plus (var 1) (var 0))) (fun x : nat => match le_lt_dec 2 x with | left _ => var x | right _ => m x end)).
apply (subAllCloseFrom LNT).
simpl in |- *.
apply H.
simpl in |- *.
induction (le_lt_dec 2 0).
elim (le_not_lt _ _ a0).
auto.
induction (le_lt_dec 2 1).
elim (le_not_lt _ _ a0).
auto.
reflexivity.
