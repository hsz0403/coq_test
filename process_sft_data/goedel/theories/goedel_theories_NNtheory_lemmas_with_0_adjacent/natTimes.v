Require Import Arith.
Require Import folLogic3.
Require Import folProp.
Require Import subProp.
Require Export NN.

Lemma natTimes : forall a b : nat, SysPrf NN (equal (Times (natToTerm a) (natToTerm b)) (natToTerm (a * b))).
Proof.
intros.
induction b as [| b Hrecb].
rewrite mult_comm.
simpl in |- *.
apply nn5.
rewrite mult_comm.
simpl in |- *.
eapply eqTrans.
apply nn6.
rewrite plus_comm.
apply eqTrans with (Plus (natToTerm (b * a)) (natToTerm a)).
apply eqPlus.
rewrite mult_comm.
apply Hrecb.
apply eqRefl.
apply natPlus.
