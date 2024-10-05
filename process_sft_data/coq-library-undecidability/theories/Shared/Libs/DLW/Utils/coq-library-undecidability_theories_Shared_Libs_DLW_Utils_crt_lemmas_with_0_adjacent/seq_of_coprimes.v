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

Theorem seq_of_coprimes n i j : i <= n -> j <= n -> i <> j -> is_gcd (1+i*fact n) (1+j*fact n) 1.
Proof.
intros H1 H2 H3.
destruct (lt_eq_lt_dec i j) as [ [] | ]; try tauto; [ | apply is_gcd_sym ]; apply seq_of_coprimes_lt; lia.
