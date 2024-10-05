Require Import Arith.
Require Import folLogic3.
Require Import folProp.
Require Import subProp.
Require Export NN.

Lemma natNE : forall a b : nat, a <> b -> SysPrf NN (notH (equal (natToTerm a) (natToTerm b))).
Proof.
assert (forall a b : nat, a < b -> SysPrf NN (notH (equal (natToTerm a) (natToTerm b)))).
intro.
induction a as [| a Hreca]; intros.
destruct b as [| n].
elim (lt_n_O _ H).
simpl in |- *.
apply impE with (notH (equal (Succ (natToTerm n)) Zero)).
apply cp2.
apply impI.
apply eqSym.
apply Axm; right; constructor.
apply nn1.
destruct b as [| n].
elim (lt_n_O _ H).
simpl in |- *.
apply impE with (notH (equal (natToTerm a) (natToTerm n))).
apply cp2.
apply nn2.
apply Hreca.
apply lt_S_n.
auto.
intros.
induction (nat_total_order _ _ H0).
apply H.
auto.
apply impE with (notH (equal (natToTerm b) (natToTerm a))).
apply cp2.
apply impI.
apply eqSym.
apply Axm; right; constructor.
apply H.
auto.
