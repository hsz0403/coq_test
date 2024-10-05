Require Import Arith.
Require Import folLogic3.
Require Import folProp.
Require Import subProp.
Require Export NN.

Lemma boundedLT : forall (m : nat) (a : Formula) (x : nat), (forall n : nat, n < m -> SysPrf NN (substituteFormula LNN a x (natToTerm n))) -> SysPrf NN (impH (LT (var x) (natToTerm m)) a).
Proof.
simple induction m; intros.
apply impI.
apply contradiction with (LT (var x) (natToTerm 0)).
apply Axm; right; constructor.
apply sysWeaken.
apply nn7.
apply impI.
eapply orE.
apply impE with (LT (var x) (natToTerm (S n))).
apply sysWeaken.
simpl in |- *.
apply nn8.
apply Axm; right; constructor.
apply sysWeaken.
apply H.
intros.
apply H0.
apply lt_S.
auto.
apply sysWeaken.
apply impI.
rewrite <- (subFormulaId LNN a x).
apply impE with (substituteFormula LNN a x (natToTerm n)).
apply (subWithEquals LNN).
apply eqSym.
apply Axm; right; constructor.
apply sysWeaken.
apply H0.
apply lt_n_Sn.
