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

Theorem CRT_bin_informative : { w | rem w u = rem a u /\ rem w v = rem b v /\ 2 < w }.
Proof.
destruct bezout_rel_prime with (1 := Huv) as (x & y & H1).
assert (rem (x*u) v = rem 1 v) as H2.
{
rewrite rem_plus_div with (a := 1) (b := u*v); auto.
rewrite <- H1; apply rem_plus_div; auto.
}
assert (rem (y*v) u = rem 1 u) as H3.
{
rewrite rem_plus_div with (a := 1) (b := u*v); auto.
rewrite <- H1, plus_comm.
apply rem_plus_div; auto.
}
exists (3*(u*v)+a*(y*v)+b*(x*u)); msplit 2.
+
rewrite <- rem_plus_rem, (mult_assoc b).
rewrite rem_scal with (k := b*x), rem_diag; auto.
rewrite Nat.mul_0_r, rem_of_0, Nat.add_0_r.
rewrite <- rem_plus_rem, rem_scal, H3, <- rem_scal, Nat.mul_1_r.
rewrite rem_plus_rem, plus_comm.
symmetry; apply rem_plus_div; auto.
+
rewrite <- plus_assoc, (plus_comm (a*_)), plus_assoc.
rewrite <- rem_plus_rem, (mult_assoc a).
rewrite rem_scal with (k := a*y), rem_diag; auto.
rewrite Nat.mul_0_r, rem_of_0, Nat.add_0_r.
rewrite <- rem_plus_rem, rem_scal, H2, <- rem_scal, Nat.mul_1_r.
rewrite rem_plus_rem, plus_comm.
symmetry; apply rem_plus_div; auto.
+
apply lt_le_trans with (3*1); try lia.
