Require Import Arith.
Require Import Wf_nat.
Require Import ZArith.
Require Import Peano_dec.
Require Import ZArith_dec.
From Pocklington Require Import gcd divides natZ prime modprime.
Require Import Max.
Definition CoPrime (a b : nat) := gcd (Z_of_nat a) (Z_of_nat b) 1.
Definition prod : forall (n : nat) (x : nat -> nat), nat.
intros.
induction n as [| n Hrecn].
exact 1.
exact (x n * Hrecn).
Defined.
Definition factorial (n : nat) : nat := prod n S.
Definition coPrimeBeta (z c : nat) : nat := S (c * S z).
Definition maxBeta (n : nat) (x : nat -> nat) : nat.
intros.
induction n as [| n Hrecn].
exact 0.
exact (max (x n) Hrecn).
Defined.

Lemma coPrimeSeqHelp : forall c i j n : nat, Divides (factorial n) c -> i < j -> i <= n -> j <= n -> CoPrime (S (c * S i)) (S (c * S j)).
Proof.
intros.
apply coPrimePrime.
intros.
induction (divdec (S (c * S i)) p).
assert (~ Divides p c).
unfold not in |- *.
intros.
assert (Divides p 1).
eapply div_plus_r.
apply div_mult_compat_l.
apply H5.
rewrite plus_comm.
simpl in |- *.
apply H4.
induction H3 as (H3, H7).
elim (lt_not_le _ _ H3).
apply div_le.
apply lt_n_Sn.
assumption.
induction (divdec (S (c * S j)) p).
assert (Divides p (c * (j - i))).
rewrite minusS.
rewrite mult_comm.
rewrite mult_minus_distr_r.
rewrite (mult_comm (S j)).
rewrite (mult_comm (S i)).
rewrite minusS.
apply div_minus_compat.
assumption.
assumption.
induction (primedivmult _ _ _ H3 H7).
elim H5.
assumption.
assert (j - i <= n).
eapply le_trans.
apply Minus.le_minus.
assumption.
elim H5.
apply div_trans with (factorial n).
apply div_trans with (j - i).
assumption.
unfold factorial in |- *.
assert (1 <= j - i).
assert (j = i + (j - i)).
apply le_plus_minus.
apply lt_le_weak.
assumption.
rewrite H10 in H0.
apply lt_n_Sm_le.
apply lt_n_S.
apply plus_lt_reg_l with i.
rewrite plus_comm.
apply H0.
replace (j - i) with (S (pred (j - i))).
apply divProd.
rewrite pred_of_minus.
apply lt_S_n.
apply le_lt_n_Sm.
replace (S (j - i - 1)) with (1 + (j - i - 1)).
rewrite <- le_plus_minus.
assumption.
assumption.
auto.
induction (j - i).
elim (le_Sn_n _ H10).
rewrite <- pred_Sn.
reflexivity.
assumption.
auto.
auto.
