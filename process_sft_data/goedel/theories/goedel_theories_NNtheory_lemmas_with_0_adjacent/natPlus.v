Require Import Arith.
Require Import folLogic3.
Require Import folProp.
Require Import subProp.
Require Export NN.

Lemma natPlus : forall a b : nat, SysPrf NN (equal (Plus (natToTerm a) (natToTerm b)) (natToTerm (a + b))).
Proof.
intros.
induction b as [| b Hrecb].
rewrite plus_comm.
simpl in |- *.
apply nn3.
rewrite plus_comm.
simpl in |- *.
apply eqTrans with (Succ (Plus (natToTerm a) (natToTerm b))).
apply nn4.
apply eqSucc.
rewrite plus_comm.
apply Hrecb.
