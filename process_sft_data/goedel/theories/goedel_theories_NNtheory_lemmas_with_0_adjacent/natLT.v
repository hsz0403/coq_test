Require Import Arith.
Require Import folLogic3.
Require Import folProp.
Require Import subProp.
Require Export NN.

Lemma natLT : forall a b : nat, a < b -> SysPrf NN (LT (natToTerm a) (natToTerm b)).
Proof.
intros.
eapply orE.
apply nn9 with (a := natToTerm b) (b := natToTerm a).
apply impI.
apply contradiction with (LT (natToTerm b) (natToTerm a)).
apply Axm; right; constructor.
apply sysWeaken.
apply natLE.
apply lt_le_weak.
auto.
apply impI.
apply orSys.
apply contradiction with (equal (natToTerm b) (natToTerm a)).
apply Axm; right; constructor.
apply sysWeaken.
apply natNE.
unfold not in |- *; intros.
apply (le_not_lt _ _ H).
rewrite H0.
apply lt_n_Sn.
apply Axm; right; constructor.
