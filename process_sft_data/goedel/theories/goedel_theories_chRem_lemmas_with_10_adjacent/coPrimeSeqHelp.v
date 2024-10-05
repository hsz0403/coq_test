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

Lemma coPrimeMult3 : forall a b c : nat, a > 0 -> b > 0 -> c > 0 -> CoPrime a c -> CoPrime b c -> CoPrime (a * b) c.
Proof.
intros.
assert (LinComb (Z_of_nat 1) (Z_of_nat a) (Z_of_nat c)).
apply gcd_lincomb_nat.
assumption.
apply H2.
assert (LinComb (Z_of_nat 1) (Z_of_nat b) (Z_of_nat c)).
apply gcd_lincomb_nat.
assumption.
apply H3.
induction H4 as (x, H4).
induction H4 as (x0, H4).
induction H5 as (x1, H5).
induction H5 as (x2, H5).
split.
split.
exists (Z.abs_nat (Z_of_nat (a * b))).
rewrite mult_1_l.
reflexivity.
exists (Z.abs_nat (Z_of_nat c)).
rewrite mult_1_l.
reflexivity.
intros.
induction H6 as (H6, H7).
set (A := Z_of_nat a) in *.
set (B := Z_of_nat b) in *.
set (C := Z_of_nat c) in *.
assert (1%Z = (A * B * (x * x1) + C * (x0 * B * x1 + x2 * A * x + x0 * x2 * C))%Z).
replace 1%Z with (Z_of_nat 1 * Z_of_nat 1)%Z.
rewrite (Zmult_comm C).
rewrite Zmult_plus_distr_l.
rewrite Zmult_plus_distr_l.
rewrite (Zplus_comm (x0 * B * x1 * C)).
rewrite Zmult_assoc_reverse.
rewrite (Zmult_assoc B).
rewrite (Zmult_comm B).
rewrite (Zmult_assoc_reverse x).
rewrite (Zmult_assoc A).
rewrite (Zmult_assoc_reverse x2).
rewrite (Zmult_comm x2).
rewrite (Zmult_assoc_reverse (A * x) x2).
repeat rewrite Zplus_assoc.
rewrite <- Zmult_plus_distr_r.
rewrite (Zmult_comm (x0 * B * x1)).
repeat rewrite (Zmult_assoc C).
rewrite (Zmult_assoc_reverse (C * x0)).
rewrite (Zmult_comm (x0 * x2)).
repeat rewrite (Zmult_assoc C).
rewrite (Zmult_assoc_reverse (C * x0)).
rewrite Zplus_assoc_reverse.
rewrite <- Zmult_plus_distr_r.
rewrite <- Zmult_plus_distr_l.
rewrite <- H4.
rewrite (Zmult_comm x2).
rewrite <- H5.
reflexivity.
auto.
assert (Divides e 1).
replace 1 with (Z.abs_nat 1).
replace e with (Z.abs_nat (Z_of_nat e)).
apply zdivdiv.
rewrite H8.
apply zdiv_plus_compat.
apply zdiv_mult_compat_l.
apply divzdiv.
unfold A, B in |- *.
rewrite <- Znat.inj_mult.
rewrite abs_inj.
assumption.
apply zdiv_mult_compat_l.
apply divzdiv.
rewrite abs_inj.
assumption.
apply abs_inj.
auto.
apply div_le.
apply lt_n_Sn.
Admitted.

Lemma multBig1 : forall a b : nat, a > 0 -> b > 0 -> a * b > 0.
Proof.
intros.
induction a as [| a Hreca].
unfold gt in H.
elim (lt_n_O _ H).
unfold gt in |- *.
apply lt_le_trans with (b * 1).
rewrite mult_1_r.
apply H0.
rewrite (mult_comm (S a)).
apply (fun m n p : nat => mult_le_compat_l p n m).
apply le_n_S.
Admitted.

Lemma prodBig1 : forall (n : nat) (x : nat -> nat), (forall z : nat, z < n -> x z > 0) -> prod n x > 0.
Proof.
intro.
induction n as [| n Hrecn].
intros.
simpl in |- *.
apply gt_Sn_n.
intros.
simpl in |- *.
apply multBig1.
apply H.
apply lt_n_Sn.
apply Hrecn.
intros.
apply H.
apply lt_S.
Admitted.

Lemma sameProd : forall (n : nat) (x1 x2 : nat -> nat), (forall z : nat, z < n -> x1 z = x2 z) -> prod n x1 = prod n x2.
Proof.
intro n.
induction n as [| n Hrecn].
intros.
auto.
intros.
simpl in |- *.
replace (x1 n) with (x2 n).
replace (prod n x1) with (prod n x2).
reflexivity.
apply Hrecn.
intros.
symmetry in |- *.
apply H.
apply lt_S.
assumption.
symmetry in |- *.
apply H.
Admitted.

Lemma coPrimeProd : forall (n : nat) (x : nat -> nat), (forall z1 z2 : nat, z1 < S n -> z2 < S n -> z1 <> z2 -> CoPrime (x z1) (x z2)) -> (forall z : nat, z < S n -> x z > 0) -> CoPrime (prod n x) (x n).
Proof.
intro.
induction n as [| n Hrecn].
intros.
simpl in |- *.
apply coPrime1.
intros.
assert (forall z1 z2 : nat, z1 < S n -> z2 < S n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
intros.
apply H.
apply lt_S.
assumption.
apply lt_S.
assumption.
assumption.
simpl in |- *.
apply coPrimeMult3.
apply H0.
apply lt_S.
apply lt_n_Sn.
apply prodBig1.
intros.
apply H0.
do 2 apply lt_S.
assumption.
apply H0.
apply lt_n_Sn.
apply H.
apply lt_S.
apply lt_n_Sn.
apply lt_n_Sn.
auto.
set (A1 := fun a : nat => match eq_nat_dec a n with | left _ => x (S n) | right _ => x a end) in *.
assert (CoPrime (prod n A1) (A1 n)).
apply Hrecn.
intros.
unfold A1 in |- *.
induction (eq_nat_dec z1 n).
induction (eq_nat_dec z2 n).
elim H4.
rewrite a0.
assumption.
apply H.
apply lt_n_Sn.
apply lt_S.
assumption.
unfold not in |- *; intros.
rewrite H5 in H3.
elim (lt_irrefl _ H3).
induction (eq_nat_dec z2 n).
apply H.
apply lt_S.
assumption.
apply lt_n_Sn.
unfold not in |- *; intros.
rewrite H5 in H2.
elim (lt_irrefl _ H2).
apply H.
apply lt_S.
assumption.
apply lt_S.
assumption.
assumption.
intros.
unfold A1 in |- *.
induction (eq_nat_dec z n).
apply H0.
apply lt_n_Sn.
apply H0.
apply lt_S.
assumption.
auto.
replace (x (S n)) with (A1 n).
replace (prod n x) with (prod n A1).
assumption.
apply sameProd.
intros.
unfold A1 in |- *.
induction (eq_nat_dec z n).
rewrite a in H3.
elim (lt_irrefl _ H3).
reflexivity.
unfold A1 in |- *.
induction (eq_nat_dec n n).
reflexivity.
elim b.
Admitted.

Lemma divProd : forall (n : nat) (x : nat -> nat) (i : nat), i < n -> Divides (x i) (prod n x).
Proof.
intro.
induction n as [| n Hrecn].
intros.
elim (lt_n_O _ H).
intros.
induction (le_lt_or_eq i n).
simpl in |- *.
rewrite mult_comm.
apply div_mult_compat_l.
apply Hrecn.
assumption.
simpl in |- *.
apply div_mult_compat_l.
rewrite H0.
apply div_refl.
apply lt_n_Sm_le.
Admitted.

Lemma chRem : forall (n : nat) (x : nat -> nat), (forall z1 z2 : nat, z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)) -> forall (y : nat -> nat) (py : forall z : nat, z < n -> y z < x z), {a : nat | a < prod n x /\ (forall (z : nat) (pz : z < n), y z = snd (proj1_sig (modulo (x z) (ltgt1 _ _ (py z pz)) a)))}.
Proof.
intro.
induction n as [| n Hrecn].
intros.
exists 0.
split.
simpl in |- *.
apply lt_O_Sn.
intros.
elim (lt_n_O _ pz).
intros.
assert (forall z1 z2 : nat, z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
intros.
apply H.
apply lt_S.
assumption.
apply lt_S.
assumption.
assumption.
assert (forall z : nat, z < n -> y z < x z).
intros.
apply py.
apply lt_S.
assumption.
induction (Hrecn x H0 y H1).
clear Hrecn.
induction p as (H2, H3).
assert (CoPrime (prod n x) (x n)).
apply coPrimeProd.
apply H.
intros.
eapply ltgt1.
apply py.
assumption.
assert (y n < x n).
apply py.
apply lt_n_Sn.
induction (chineseRemainderTheorem (prod n x) (x n) H4 x0 (y n) H2 H5).
exists x1.
induction p as (H6, H7).
induction H7 as (H7, H8).
split.
simpl in |- *.
rewrite mult_comm.
assumption.
intros.
induction (le_lt_or_eq z n).
assert (y z = snd (proj1_sig (modulo (x z) (ltgt1 (y z) (x z) (H1 z H9)) x0))).
apply H3.
induction (modulo (x z) (ltgt1 (y z) (x z) (H1 z H9)) x0).
simpl in H10.
induction (modulo (x z) (ltgt1 (y z) (x z) (py z pz)) x1).
simpl in |- *.
rewrite H10.
induction (modulo (prod n x) (ltgt1 x0 (prod n x) H2) x1).
simpl in H7.
rewrite H7 in p.
induction p1 as (H11, H12).
induction p as (H13, H14).
induction p0 as (H15, H16).
rewrite H13 in H11.
apply uniqueRem with (x z) x1.
apply (ltgt1 (y z) (x z) (py z pz)).
assert (Divides (x z) (prod n x)).
apply divProd.
assumption.
induction H17 as (x5, H17).
rewrite H17 in H11.
rewrite (mult_comm (x z)) in H11.
rewrite mult_assoc in H11.
rewrite plus_assoc in H11.
rewrite <- mult_plus_distr_r in H11.
exists (fst x4 * x5 + fst x2).
split.
apply H11.
assumption.
exists (fst x3).
auto.
induction (modulo (x z) (ltgt1 (y z) (x z) (py z pz)) x1).
induction (modulo (x n) (ltgt1 (y n) (x n) H5) x1).
simpl in H8.
simpl in |- *.
rewrite H9.
rewrite H8.
eapply uniqueRem.
apply (ltgt1 (y n) (x n) H5).
exists (fst x3).
apply p0.
exists (fst x2).
rewrite H9 in p.
assumption.
apply lt_n_Sm_le.
Admitted.

Lemma minusS : forall a b : nat, b - a = S b - S a.
Proof.
intros.
replace (S b) with (1 + b).
replace (S a) with (1 + a).
rewrite <- minus_plus_simpl_l_reverse.
reflexivity.
auto.
Admitted.

Lemma primeDiv : forall a : nat, 1 < a -> exists p : nat, Prime p /\ Divides p a.
intro a.
apply (lt_wf_ind a).
clear a.
intros.
induction (primedec n).
exists n.
split.
assumption.
exists 1.
symmetry in |- *.
apply mult_1_r.
induction (nonprime_witness _ H0 H1).
induction H2 as (H2, H3).
induction H3 as (H3, H4).
induction (H _ H3 H2).
exists x0.
induction H5 as (H5, H6).
split.
assumption.
eapply div_trans.
apply H6.
Admitted.

Lemma coPrimePrime : forall a b : nat, (forall p : nat, Prime p -> ~ Divides p a \/ ~ Divides p b) -> CoPrime a b.
Proof.
intros.
unfold CoPrime in |- *.
split.
split.
exists a.
rewrite mult_1_l.
apply abs_inj.
exists b.
rewrite mult_1_l.
apply abs_inj.
intros.
induction H0 as (H0, H1).
rewrite abs_inj in H0.
rewrite abs_inj in H1.
induction (le_or_lt e 1).
assumption.
induction (primeDiv _ H2).
induction H3 as (H3, H4).
induction (H _ H3).
elim H5.
eapply div_trans.
apply H4.
assumption.
elim H5.
eapply div_trans.
apply H4.
Admitted.

Lemma coPrimeSeq : forall c i j n : nat, Divides (factorial n) c -> i <> j -> i <= n -> j <= n -> CoPrime (coPrimeBeta i c) (coPrimeBeta j c).
Proof.
unfold coPrimeBeta in |- *.
intros.
induction (nat_total_order _ _ H0).
eapply coPrimeSeqHelp.
apply H.
assumption.
assumption.
assumption.
apply coPrimeSym.
eapply coPrimeSeqHelp.
apply H.
assumption.
assumption.
Admitted.

Lemma gtBeta : forall z c : nat, coPrimeBeta z c > 0.
Proof.
unfold coPrimeBeta in |- *.
intros.
Admitted.

Definition maxBeta (n : nat) (x : nat -> nat) : nat.
intros.
induction n as [| n Hrecn].
exact 0.
Admitted.

Lemma maxBetaLe : forall (n : nat) (x : nat -> nat) (i : nat), i < n -> x i <= maxBeta n x.
Proof.
simple induction n.
intros.
elim (lt_n_O _ H).
intros.
simpl in |- *.
induction (le_lt_or_eq i n0).
eapply le_trans.
apply H.
assumption.
apply le_max_r.
rewrite H1.
apply le_max_l.
apply lt_n_Sm_le.
Admitted.

Theorem divProd2 : forall (n : nat) (x : nat -> nat) (i : nat), i <= n -> Divides (prod i x) (prod n x).
Proof.
simple induction n.
intros.
assert (0 = i).
apply le_n_O_eq.
assumption.
rewrite H0.
apply div_refl.
intros.
induction (le_lt_or_eq i (S n0)).
simpl in |- *.
rewrite mult_comm.
apply div_mult_compat_l.
apply H.
apply lt_n_Sm_le.
assumption.
rewrite H1.
apply div_refl.
Admitted.

Theorem betaTheorem1 : forall (n : nat) (y : nat -> nat), {a : nat * nat | forall z : nat, z < n -> y z = snd (proj1_sig (modulo (coPrimeBeta z (snd a)) (gtBeta z (snd a)) (fst a)))}.
Proof.
intros.
set (c := factorial (max n (maxBeta n y))) in *.
set (x := fun z : nat => coPrimeBeta z c) in *.
assert (forall z1 z2 : nat, z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
intros.
unfold x in |- *.
eapply coPrimeSeq.
eapply div_trans.
unfold factorial in |- *.
apply divProd2.
apply le_max_l.
unfold c, factorial in |- *.
apply div_refl.
assumption.
apply lt_le_weak.
assumption.
apply lt_le_weak.
assumption.
assert (forall z : nat, z < n -> y z < x z).
intros.
unfold x, coPrimeBeta in |- *.
apply le_lt_n_Sm.
induction (mult_O_le c (S z)).
discriminate H1.
apply le_trans with c.
unfold c in |- *.
apply le_trans with (max n (maxBeta n y)).
apply le_trans with (maxBeta n y).
apply maxBetaLe.
assumption.
apply le_max_r.
generalize (max n (maxBeta n y)).
intros.
induction n0 as [| n0 Hrecn0].
simpl in |- *.
apply le_n_Sn.
induction n0 as [| n0 Hrecn1].
simpl in |- *.
apply le_n.
assert (factorial n0 > 0).
unfold factorial in |- *.
apply prodBig1.
intros.
apply gt_Sn_O.
simpl in |- *.
eapply le_trans with (1 + (1 + n0 * (factorial n0 + n0 * factorial n0))).
simpl in |- *.
repeat apply le_n_S.
induction (mult_O_le n0 (factorial n0 + n0 * factorial n0)).
unfold gt in H2.
assert (factorial n0 = factorial n0 + 0).
rewrite plus_comm.
auto.
assert (0 < factorial n0).
assumption.
rewrite H4 in H2.
set (A1 := factorial n0 + 0) in *.
rewrite <- H3 in H2.
unfold A1 in H2.
clear H4 A1.
assert (n0 * factorial n0 < 0).
eapply plus_lt_reg_l.
apply H2.
elim (lt_n_O _ H4).
rewrite mult_comm.
assumption.
apply plus_le_compat.
apply le_plus_trans.
apply lt_n_Sm_le.
apply lt_n_S.
assumption.
apply plus_le_compat.
apply le_plus_trans.
apply lt_n_Sm_le.
apply lt_n_S.
assumption.
apply le_n.
rewrite mult_comm.
assumption.
induction (chRem _ _ H _ H0).
exists (x0, c).
intros.
induction p as (H2, H3).
rewrite (H3 z H1).
induction (modulo (x z) (ltgt1 (y z) (x z) (H0 z H1)) x0).
replace (snd (x0, c)) with c.
replace (fst (x0, c)) with x0.
induction (modulo (coPrimeBeta z c) (gtBeta z c) x0).
simpl in |- *.
eapply uniqueRem.
apply gtBeta.
unfold x in p.
exists (fst x1).
apply p.
exists (fst x2).
apply p0.
auto.
Admitted.

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
