Require Import List Arith Lia Permutation Extraction.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat gcd prime binomial.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
Set Implicit Arguments.
Section Informative_Chinese_Remainder_theorems.
Hint Resolve divides_refl divides_mult divides_mult_r : core.
Section Binary.
Variable (u v a b : nat) (Hu : u <> 0) (Hv : v <> 0) (Huv : is_gcd u v 1).
End Binary.
End Informative_Chinese_Remainder_theorems.
Section sequence_of_coprimes.
Let seq_of_coprimes_lt n i j : i < j <= n -> is_gcd (1+i*fact n) (1+j*fact n) 1.
Proof.
intros (H1 & H2).
apply no_common_prime_is_coprime; try discriminate.
intros p Hp H3 H4.
assert (divides p ((j-i)*fact n)) as H5.
{
replace ((j-i)*fact n) with (1+j*fact n - (1+i*fact n)).
+
apply divides_minus; auto.
+
rewrite Nat.mul_sub_distr_r; lia.
}
assert (~ divides p (fact n)) as H6.
{
intros H6.
rewrite plus_comm in H3.
apply divides_plus_inv in H3.
+
apply divides_1_inv, Hp in H3; trivial.
+
apply divides_mult; trivial.
}
apply prime_div_mult with (1 := Hp) in H5.
destruct H5 as [ H5 | H5 ]; try tauto.
apply H6, divides_fact.
assert (p <> 0) as H7.
{
apply prime_ge_2 in Hp; lia.
}
destruct Hp.
split; try lia.
apply divides_le in H5; lia.
End sequence_of_coprimes.
Section Godel_beta.
Definition godel_beta a b n := rem a (S ((S n)*b)).
End Godel_beta.

Theorem CRT_informative n (m v : vec nat n) : (forall p, vec_pos m p <> 0) -> (forall p q, p <> q -> is_gcd (vec_pos m p) (vec_pos m q) 1) -> { w | forall p, rem w (vec_pos m p) = rem (vec_pos v p) (vec_pos m p) }.
Proof.
destruct n as [ | n ]; [ exists 0; intros p; invert pos p | ].
revert m v.
induction n as [ | n IHn ]; intros m v H1 H2.
+
exists (vec_pos v pos0); intros p; invert pos p; auto.
invert pos p.
+
revert H1 H2.
vec split m with m1.
vec split m with m2.
vec split v with v1.
vec split v with v2.
intros H1 H2.
generalize (H1 pos0) (H1 pos1) (H2 pos0 pos1); intros Hm1 Hm2 H12; simpl in Hm1, Hm2, H12.
destruct (@CRT_bin_informative m1 m2 v1 v2) as (w0 & H3 & H4 & _); auto.
{
apply H12; discriminate.
}
destruct (IHn (m1*m2 ## m) (w0 ## v)) as (w & Hw).
*
intros p; invert pos p.
-
assert (0 < m1 * m2); try lia.
-
apply H1 with (p := pos_nxt (pos_nxt p)).
*
intros p q; invert pos p; invert pos q; intros H; try (destruct H; auto; fail).
2: apply is_gcd_sym.
1,2: apply rel_prime_mult; [ apply (H2 pos0 (pos_nxt (pos_nxt _))) | apply (H2 pos1 (pos_nxt (pos_nxt _))) ]; discriminate.
apply (H2 (pos_nxt (pos_nxt _)) (pos_nxt (pos_nxt _))).
contradict H; apply pos_nxt_inj in H; auto.
*
exists w.
intros p; repeat invert pos p.
-
rewrite <- H3.
generalize (Hw pos0); simpl.
apply divides_rem_congr, divides_mult_r, divides_refl.
-
rewrite <- H4.
generalize (Hw pos0); simpl.
apply divides_rem_congr, divides_mult, divides_refl.
-
apply Hw with (p := pos_nxt _).
