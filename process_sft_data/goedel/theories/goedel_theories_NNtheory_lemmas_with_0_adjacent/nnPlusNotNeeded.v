Require Import Arith.
Require Import folLogic3.
Require Import folProp.
Require Import subProp.
Require Export NN.

Lemma nnPlusNotNeeded : forall n : nat, SysPrf NN (impH (orH (LT (var 1) (natToTerm n)) (equal (var 1) (natToTerm n))) (LT (var 1) (Succ (natToTerm n)))).
Proof.
intros.
induction n as [| n Hrecn].
simpl in |- *.
apply impI.
apply orSys.
apply contradiction with (LT (var 1) Zero).
apply Axm; right; constructor.
apply sysWeaken.
apply nn7.
rewrite <- (subFormulaId LNN (LT (var 1) (Succ Zero)) 1).
apply impE with (substituteFormula LNN (LT (var 1) (Succ Zero)) 1 Zero).
apply (subWithEquals LNN).
apply eqSym.
apply Axm; right; constructor.
apply sysWeaken.
replace (substituteFormula LNN (LT (var 1) (Succ Zero)) 1 Zero) with (LT (natToTerm 0) (natToTerm 1)).
apply natLT.
auto.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
reflexivity.
simpl in |- *.
apply impI.
apply orSys.
apply impE with (orH (LT (var 1) (natToTerm n)) (equal (var 1) (natToTerm n))).
apply sysWeaken.
apply impTrans with (LT (var 1) (natToTerm (S n))).
apply Hrecn.
apply boundedLT.
intros.
replace (substituteFormula LNN (LT (var 1) (Succ (Succ (natToTerm n)))) 1 (natToTerm n0)) with (LT (natToTerm n0) (natToTerm (S (S n)))).
apply natLT.
apply lt_S.
assumption.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
rewrite (subTermNil LNN).
reflexivity.
apply closedNatToTerm.
apply impE with (LT (var 1) (Succ (natToTerm n))).
apply sysWeaken.
apply nn8.
apply Axm; right; constructor.
rewrite <- (subFormulaId LNN (LT (var 1) (Succ (Succ (natToTerm n)))) 1).
apply impE with (substituteFormula LNN (LT (var 1) (Succ (Succ (natToTerm n)))) 1 (Succ (natToTerm n))).
apply (subWithEquals LNN).
apply eqSym.
apply Axm; right; constructor.
apply sysWeaken.
replace (substituteFormula LNN (LT (var 1) (Succ (Succ (natToTerm n)))) 1 (Succ (natToTerm n))) with (LT (natToTerm (S n)) (natToTerm (S (S n)))).
apply natLT.
apply lt_n_Sn.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
rewrite (subTermNil LNN).
reflexivity.
apply closedNatToTerm.
