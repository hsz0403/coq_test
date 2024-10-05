Require Import Arith.
Require Import folLogic3.
Require Import folProp.
Require Import subProp.
Require Export NN.

Lemma natLE : forall a b : nat, b <= a -> SysPrf NN (notH (LT (natToTerm a) (natToTerm b))).
Proof.
intros.
induction b as [| b Hrecb].
apply nn7.
simpl in |- *.
apply impE with (notH (orH (LT (natToTerm a) (natToTerm b)) (equal (natToTerm a) (natToTerm b)))).
apply cp2.
apply nn8.
apply nOr.
apply andI.
apply Hrecb.
apply le_S_n.
apply le_S.
auto.
apply natNE.
unfold not in |- *; intros.
apply (le_not_lt _ _ H).
rewrite H0.
apply lt_n_Sn.
