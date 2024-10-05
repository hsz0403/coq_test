Require Import Arith ZArith Lia List.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list gcd prime php utils_nat.
From Undecidability.H10.ArithLibs Require Import Zp.
Set Implicit Arguments.
Set Default Proof Using "Type".
Section utils.
Fact prime_2_or_odd p : prime p -> p = 2 \/ exists n, 0 < n /\ p = 2*n+1.
Proof.
intros Hp.
assert (H1 : p <> 0).
{
generalize (prime_ge_2 Hp); lia.
}
assert (H3 : 2 <> 0) by discriminate.
destruct (eq_nat_dec p 2) as [ | H2 ]; auto; right.
assert (rem p 2 = 1) as Hp1.
{
generalize (div_rem_spec2 p H3).
case_eq (rem p 2).
+
intros H _.
apply divides_rem_eq in H.
apply proj2 in Hp.
destruct (Hp _ H); subst; lia.
+
intros; lia.
}
exists (div p 2); split.
+
generalize (div_rem_spec1 p 2) (prime_ge_2 Hp).
destruct (div p 2); intros; lia.
+
rewrite mult_comm.
rewrite (div_rem_spec1 p 2) at 1.
f_equal; auto.
Fact remarkable_id1_nat x y : (x+y)*(x+y) = x*x+2*(x*y)+y*y.
Proof.
ring.
Fact remarkable_id1_Z (a b : Z) : ((a+b)*(a+b) = a*a + 2*a*b + b*b)%Z.
Proof.
ring.
Fact Zsquare_bound x y : (-y <= x <= y -> x*x <= y*y)%Z.
Proof.
intros (H1 & H2).
destruct (Z_pos_or_neg x).
+
apply Z.square_le_mono_nonneg; auto.
+
replace (y*y)%Z with ((-y)*(-y))%Z by ring.
apply Z.square_le_mono_nonpos; lia.
Local Fact bounded_upper_limit_4 a b c d m : (a <= m -> b <= m -> c <= m -> d <= m -> a+b+c+d = 4*m -> a = m /\ b = m /\ c = m /\ d = m)%Z.
Proof.
lia.
Local Fact bounded_lower_limit_4 a b c d : (0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> a+b+c+d = 0 -> a = 0 /\ b = 0 /\ c = 0 /\ d = 0)%Z.
Proof.
lia.
Local Fact four_squares_zero a b c d : (a*a+b*b+c*c+d*d = 0 -> a = 0 /\ b = 0 /\ c = 0 /\ d = 0)%Z.
Proof.
intros H.
apply bounded_lower_limit_4 in H; try apply Z.square_nonneg.
destruct H as (H1 & H2 & H3 & H4).
apply Zmult_integral in H1.
apply Zmult_integral in H2.
apply Zmult_integral in H3.
apply Zmult_integral in H4.
destruct H1; destruct H2; destruct H3; destruct H4; auto.
Fact Zsquare_inj x y : (x*x = y*y -> { x = y } + { - x = y } )%Z.
Proof.
intros H.
assert ( (x+y)*(x-y) = 0 )%Z as E.
{
rewrite Z.mul_sub_distr_l, !Z.mul_add_distr_r, H; ring.
}
apply Zmult_integral in E.
destruct (Z.eq_dec x y); auto.
right; lia.
Fact square_4_simpl x m : (4*(x*x) = Z.of_nat m*Z.of_nat m)%Z -> { n | m = 2*n /\ (x = Z.of_nat n \/ (x = - Z.of_nat n)%Z) }.
Proof.
intros H.
replace (4*(x*x))%Z with ((2*x)*(2*x))%Z in H by ring.
apply Zsquare_inj in H.
destruct H as [ H | H ].
+
destruct Z_of_nat_complete_inf with x as (k & ->).
*
generalize (Zle_0_nat m); lia.
*
exists k; split; auto.
apply Nat2Z.inj.
rewrite Nat2Z.inj_mul, <- H; auto.
+
destruct (Z_of_nat_complete_inf (Z.opp x)) as (k & Hk).
*
generalize (Zle_0_nat m); lia.
*
exists k; split.
-
apply Nat2Z.inj.
rewrite Nat2Z.inj_mul, <- H, <- Hk; ring.
-
right; rewrite <- Hk; ring.
Fact square_4_simpl' x m : (4*(x*x) = Z.of_nat (2*m)*Z.of_nat (2*m) -> x = Z.of_nat m \/ x = - Z.of_nat m)%Z.
Proof.
intros H.
replace (4*(x*x))%Z with ((2*x)*(2*x))%Z in H by ring.
apply Zsquare_inj in H.
destruct H as [ H | H ]; rewrite Nat2Z.inj_mul in H; change (Z.of_nat 2) with 2%Z in H; lia.
End utils.
Section half_modulus_lemma.
Variable (m : nat) (H2m : 2*m <> 0) (Hm2 : 4*m*m <> 0).
Let lemma1 x : Z2Zp H2m x = nat2Zp H2m m -> Z2Zp Hm2 (x*x) = nat2Zp Hm2 (m*m).
Proof.
intros H.
rewrite <- Z2Zp_of_nat in H.
apply Z2Zp_inj in H.
destruct H as (k & H).
assert (x = Z.of_nat m+2*k*Z.of_nat m)%Z as Hx.
{
rewrite Nat2Z.inj_mul, Zmult_assoc, (Zmult_comm k) in H.
change 2%Z with (Z.of_nat 2); lia.
}
rewrite Hx, remarkable_id1_Z, !Z2Zp_plus.
replace (2*Z.of_nat m * (2*k*Z.of_nat m))%Z with (Z.of_nat (4*m*m)*k)%Z.
2:{
rewrite !Nat2Z.inj_mul; ring.
}
replace (2*k*Z.of_nat m * (2*k*Z.of_nat m))%Z with (Z.of_nat (4*m*m)*(k*k))%Z.
2:{
rewrite !Nat2Z.inj_mul; ring.
}
rewrite (Z2Zp_mult _ _ k), Z2Zp_of_nat, nat2Zp_p, Zp_mult_zero.
rewrite (Z2Zp_mult _ _ (k*k)), Z2Zp_of_nat, nat2Zp_p, Zp_mult_zero.
rewrite !Zp_plus_zero_r, <- Nat2Z.inj_mul, Z2Zp_of_nat; auto.
Let lemma2 x : (Z2Zp H2m x = Zp_opp H2m (nat2Zp H2m m))%Z -> Z2Zp Hm2 (x*x) = nat2Zp Hm2 (m*m).
Proof.
intros H.
replace (x*x)%Z with ((-x)*(-x))%Z by ring.
apply lemma1.
rewrite Z2Zp_opp, H, Zp_opp_inv; auto.
Fact half_modulus_lemma' x : Z2Zp H2m x = nat2Zp H2m m \/ (Z2Zp H2m x = Zp_opp H2m (nat2Zp H2m m))%Z -> Z2Zp Hm2 (x*x) = nat2Zp Hm2 (m*m).
Proof.
intros []; auto.
Fact half_modulus_lemma x y : Z2Zp H2m x = Z2Zp H2m y -> y = Z.of_nat m \/ y = (- Z.of_nat m)%Z -> Z2Zp Hm2 (x*x) = nat2Zp Hm2 (m*m).
Proof.
intros H1 H2.
apply half_modulus_lemma'.
rewrite H1.
destruct H2; subst y; [ left | right ].
+
rewrite Z2Zp_of_nat; auto.
+
rewrite Z2Zp_opp, Z2Zp_of_nat; auto.
End half_modulus_lemma.
Section lagrange_prelim_odd.
Variable (p n : nat) (Hp1 : prime p) (Hp2 : p = 2*n+1).
Let Hn : 0 < n.
Proof.
destruct n; try lia.
simpl in Hp2; subst.
exfalso; apply Hp1; trivial.
Let Hp : p <> 0.
Proof.
lia.
Let l := list_an 0 (1+n).
Let Hl : forall x, In x l <-> x <= n.
Proof.
unfold l; intros x; rewrite list_an_spec; lia.
Let f x := nat2Zp Hp (x*x).
Let g y := Zp_opp Hp (Zp_plus Hp (Zp_one Hp) (f y)).
Let Hf x y : In x l -> In y l -> f x = f y -> x = y.
Proof.
unfold f; intros G1 G2 H.
do 2 rewrite nat2Zp_mult in H.
apply Zp_prime_square_eq_square in H; auto.
destruct H as [ H | H ].
+
rewrite nat2Zp_inj in H.
rewrite <- (@rem_idem x p), H, rem_idem; auto.
*
apply Hl in G2; lia.
*
apply Hl in G1; lia.
+
apply f_equal with (f := @proj1_sig _ _) in H; simpl in H.
rewrite rem_idem in H.
2: apply Hl in G1; lia.
case_eq (rem y p).
*
intros Hy.
rewrite Hy, Nat.sub_0_r, rem_diag in H; auto.
rewrite rem_idem in Hy; try lia.
apply Hl in G2; lia.
*
intros w Hw.
rewrite rem_idem in H; try lia.
rewrite H.
apply Hl in G2.
apply Hl in G1.
rewrite rem_idem in H; lia.
Let Hg x y : In x l -> In y l -> g x = g y -> x = y.
Proof.
unfold g; intros G1 G2 G3.
apply Zp_opp_inj, Zp_plus_inj_l in G3.
revert G3; apply Hf; auto.
Let intersection : exists y, In y (map f l) /\ In y (map g l).
Proof.
destruct partition_intersection with (l := map f l) (m := map g l) (k := Zp_list Hp) as [ G | [ G | ] ]; auto.
*
rewrite Zp_list_length, app_length, map_length, map_length.
unfold l; rewrite list_an_length; lia.
*
intros ? _; apply Zp_list_spec.
*
apply list_has_dup_map_inv in G; auto.
apply not_list_has_dup_an in G; tauto.
*
apply list_has_dup_map_inv in G; auto.
apply not_list_has_dup_an in G; tauto.
Local Lemma lagrange_prelim_odd : exists a b, divides p (1+a*a+b*b) /\ 2*a <= p-1 /\ 2*b <= p-1.
Proof using Hf.
destruct intersection as (u & G1 & G2).
rewrite in_map_iff in G1.
rewrite in_map_iff in G2.
destruct G1 as (a & G3 & G4).
destruct G2 as (b & G5 & G6).
exists a, b; msplit 2.
+
rewrite divides_nat2Zp with (Hp := Hp), (plus_comm 1), <- plus_assoc, !nat2Zp_plus, nat2Zp_one.
fold (f a).
apply Zp_opp_plus_eq.
fold (f b); fold (g b).
now rewrite G3, G5, Zp_plus_zero.
+
apply Hl in G4; lia.
+
apply Hl in G6; lia.
End lagrange_prelim_odd.
Local Notation four_squares := (fun a b c d => a*a+b*b+c*c+d*d)%Z.
Fact Euler_squares x y a1 b1 c1 d1 a2 b2 c2 d2 : (x = four_squares a1 b1 c1 d1 -> y = four_squares a2 b2 c2 d2 -> x*y = four_squares (a1*a2+b1*b2+c1*c2+d1*d2) (a1*b2-b1*a2+d1*c2-c1*d2) (a1*c2-c1*a2+b1*d2-d1*b2) (a1*d2-d1*a2+c1*b2-b1*c2))%Z.
Proof.
intros -> ->; ring.
Section lagrange_for_primes.
Variable (p : nat) (Hp : prime p).
Let P n := exists a b c d, Z.of_nat (n*p) = four_squares a b c d.
Section lagrange_prime_step.
Variable (m : nat) (H1 : m < p) (H3 : 1 < m) (x1 x2 x3 x4 : Z) (H2 : Z.of_nat (m*p) = four_squares x1 x2 x3 x4).
Let Hm : m <> 0.
Proof.
lia.
Local Fact lagrange_prime_step' : exists r, 1 <= r < m /\ P r.
Proof using H1 H2 H3 Hp.
generalize (Zp_small_repr Hm x1) (Zp_small_repr Hm x2) (Zp_small_repr Hm x3) (Zp_small_repr Hm x4).
intros (y1 & E1 & Q1) (y2 & E2 & Q2) (y3 & E3 & Q3) (y4 & E4 & Q4).
assert (Z2Zp Hm (y1*y1+y2*y2+y3*y3+y4*y4) = Zp_zero Hm) as H4.
{
rewrite !Z2Zp_plus, !Z2Zp_mult, <- E1, <- E2, <- E3, <- E4.
rewrite <- !Z2Zp_mult, <- !Z2Zp_plus, <- H2.
rewrite Nat2Z.inj_mul, Z2Zp_mult.
rewrite Z2Zp_of_nat, nat2Zp_p, Zp_mult_zero; auto.
}
apply Z2Zp_zero_inv in H4.
destruct H4 as (r' & Hr).
rewrite (Zmult_comm _ r') in Hr.
assert (4 * (r' * Z.of_nat m) <= 4 * (Z.of_nat m * Z_of_nat m))%Z as Hr'.
{
rewrite <- Hr, !Z.mul_add_distr_l; lia.
}
rewrite !(Zmult_comm 4) in Hr'.
apply Zmult_le_reg_r in Hr'; try lia.
apply Zmult_le_reg_r in Hr'; try lia.
assert (0 <= r' * Z_of_nat m)%Z as Hr''.
{
rewrite <- Hr; repeat apply Z.add_nonneg_nonneg; apply Z.square_nonneg.
}
apply Zmult_le_0_reg_r in Hr''.
2:{
apply (inj_gt m 0); lia.
}
apply Z_of_nat_complete_inf in Hr''.
destruct Hr'' as (r & ?); subst r'.
apply Nat2Z.inj_le in Hr'.
destruct (eq_nat_dec m r) as [ <- | Hr1 ].
{
clear Hr'.
apply f_equal with (f := fun i => (4*i)%Z) in Hr.
rewrite !Z.mul_add_distr_l in Hr.
apply bounded_upper_limit_4 in Hr; auto.
destruct Hr as (F1 & F2 & F3 & F4).
apply square_4_simpl in F1.
destruct F1 as (q & Hq & F1).
rewrite Hq in F2, F3, F4.
apply square_4_simpl' in F2.
apply square_4_simpl' in F3.
apply square_4_simpl' in F4.
subst m.
assert (4*q*q <> 0) as Hq.
{
destruct q; simpl; try discriminate; lia.
}
apply half_modulus_lemma with (1 := E1) (Hm2 := Hq) in F1.
apply half_modulus_lemma with (1 := E2) (Hm2 := Hq) in F2.
apply half_modulus_lemma with (1 := E3) (Hm2 := Hq) in F3.
apply half_modulus_lemma with (1 := E4) (Hm2 := Hq) in F4.
assert (Z2Zp Hq (Z.of_nat (2 * q * p)) = Zp_zero Hq) as C.
{
rewrite H2, !Z2Zp_plus, F1, F2, F3, F4.
rewrite <- !nat2Zp_plus.
replace (q*q+q*q+q*q+q*q) with (4*q*q) by ring.
rewrite nat2Zp_p; auto.
}
rewrite Z2Zp_of_nat in C.
apply divides_nat2Zp in C.
destruct C as (d & Hd).
assert (divides (2*q) p) as C.
{
replace (d*(4*q*q)) with (2*q*(d*(2*q))) in Hd by ring.
apply Nat.mul_cancel_l in Hd; try lia.
exists d; auto.
}
apply Hp in C; destruct C; try lia.
}
destruct (eq_nat_dec r 0) as [ -> | Hr2 ].
{
apply four_squares_zero in Hr.
destruct Hr as (? & ? & ? & ?); subst y1 y2 y3 y4.
assert (Hm2 : m*m <> 0).
{
destruct m; simpl; try discriminate; lia.
}
rewrite Z2Zp_zero in E1; apply Zp_square_zero with (Hm2 := Hm2) in E1.
rewrite Z2Zp_zero in E2; apply Zp_square_zero with (Hm2 := Hm2) in E2.
rewrite Z2Zp_zero in E3; apply Zp_square_zero with (Hm2 := Hm2) in E3.
rewrite Z2Zp_zero in E4; apply Zp_square_zero with (Hm2 := Hm2) in E4.
assert (Z2Zp Hm2 (Z.of_nat (m*p)) = Zp_zero Hm2) as C.
{
rewrite H2, !Z2Zp_plus, E1, E2, E3, E4, !Zp_plus_zero; auto.
}
rewrite Z2Zp_of_nat in C.
apply divides_nat2Zp in C.
destruct C as (d & Hd).
assert (divides m p) as C.
{
replace (d*(m*m)) with (m*(d*m)) in Hd by ring.
apply Nat.mul_cancel_l in Hd; try lia.
exists d; auto.
}
apply Hp in C.
destruct C as [ C | C ]; lia.
}
assert (0 < r < m) as Hk by lia.
clear Hr' Hr1 Hr2 Q1 Q2 Q3 Q4.
symmetry in Hr.
rewrite <- Nat2Z.inj_mul in Hr.
assert (exists a b c d, Z.of_nat (r*p*m*m) = four_squares a b c d%Z /\ Z2Zp Hm a = Zp_zero Hm /\ Z2Zp Hm b = Zp_zero Hm /\ Z2Zp Hm c = Zp_zero Hm /\ Z2Zp Hm d = Zp_zero Hm) as Q.
{
exists (x1 * y1 + x2 * y2 + x3 * y3 + x4 * y4)%Z, (x1 * y2 - x2 * y1 + x4 * y3 - x3 * y4)%Z, (x1 * y3 - x3 * y1 + x2 * y4 - x4 * y2)%Z, (x1 * y4 - x4 * y1 + x3 * y2 - x2 * y3)%Z; msplit 4.
+
rewrite <- (Euler_squares _ _ _ _ _ _ _ _ H2 Hr).
rewrite <- Nat2Z.inj_mul; f_equal; ring.
+
rewrite !Z2Zp_plus, !Z2Zp_mult.
rewrite <- E1, <- E2, <- E3, <- E4.
rewrite <- !Z2Zp_mult, <- !Z2Zp_plus.
rewrite <- H2, Nat2Z.inj_mul, Z2Zp_mult, Z2Zp_of_nat, nat2Zp_p, Zp_mult_zero; auto.
+
repeat (rewrite !Z2Zp_minus || rewrite !Z2Zp_plus).
rewrite !Z2Zp_mult.
rewrite <- E1, <- E2, <- E3, <- E4.
rewrite <- !Z2Zp_mult.
repeat (rewrite <- !Z2Zp_minus || rewrite <- !Z2Zp_plus).
rewrite <- Z2Zp_zero; f_equal; ring.
+
repeat (rewrite !Z2Zp_minus || rewrite !Z2Zp_plus).
rewrite !Z2Zp_mult.
rewrite <- E1, <- E2, <- E3, <- E4.
rewrite <- !Z2Zp_mult.
repeat (rewrite <- !Z2Zp_minus || rewrite <- !Z2Zp_plus).
rewrite <- Z2Zp_zero; f_equal; ring.
+
repeat (rewrite !Z2Zp_minus || rewrite !Z2Zp_plus).
rewrite !Z2Zp_mult.
rewrite <- E1, <- E2, <- E3, <- E4.
rewrite <- !Z2Zp_mult.
repeat (rewrite <- !Z2Zp_minus || rewrite <- !Z2Zp_plus).
rewrite <- Z2Zp_zero; f_equal; ring.
}
clear x1 x2 x3 x4 H2 H3 y1 E1 y2 E2 y3 E3 y4 E4 Hr.
destruct Q as (a & b & c & d & H & Ha & Hb & Hc & Hd).
apply Z2Zp_zero_inv in Ha; destruct Ha as (x & ->).
apply Z2Zp_zero_inv in Hb; destruct Hb as (y & ->).
apply Z2Zp_zero_inv in Hc; destruct Hc as (z & ->).
apply Z2Zp_zero_inv in Hd; destruct Hd as (w & ->).
exists r; split; try lia.
exists x, y, z, w.
apply Z.mul_cancel_r with (p := Z.of_nat (m*m)).
{
intros E.
apply Nat2Z.inj with (m := 0) in E.
destruct m; try discriminate; lia.
}
rewrite <- Nat2Z.inj_mul, mult_assoc, H.
rewrite Nat2Z.inj_mul; ring.
End lagrange_prime_step.
Let lagrange_prime_step m : 1 < m < p -> P m -> exists r, 1 <= r < m /\ P r.
Proof.
intros H1 (x1 & x2 & x3 & x4 & H2); apply lagrange_prime_step' with (3 := H2); lia.
End lagrange_for_primes.
Section lagrange.
Open Scope Z_scope.
End lagrange.

Fact prime_2_or_odd p : prime p -> p = 2 \/ exists n, 0 < n /\ p = 2*n+1.
Proof.
intros Hp.
assert (H1 : p <> 0).
{
generalize (prime_ge_2 Hp); lia.
}
assert (H3 : 2 <> 0) by discriminate.
destruct (eq_nat_dec p 2) as [ | H2 ]; auto; right.
assert (rem p 2 = 1) as Hp1.
{
generalize (div_rem_spec2 p H3).
case_eq (rem p 2).
+
intros H _.
apply divides_rem_eq in H.
apply proj2 in Hp.
destruct (Hp _ H); subst; lia.
+
intros; lia.
}
exists (div p 2); split.
+
generalize (div_rem_spec1 p 2) (prime_ge_2 Hp).
destruct (div p 2); intros; lia.
+
rewrite mult_comm.
rewrite (div_rem_spec1 p 2) at 1.
Admitted.

Fact remarkable_id1_nat x y : (x+y)*(x+y) = x*x+2*(x*y)+y*y.
Proof.
Admitted.

Fact remarkable_id1_Z (a b : Z) : ((a+b)*(a+b) = a*a + 2*a*b + b*b)%Z.
Proof.
Admitted.

Fact Zsquare_bound x y : (-y <= x <= y -> x*x <= y*y)%Z.
Proof.
intros (H1 & H2).
destruct (Z_pos_or_neg x).
+
apply Z.square_le_mono_nonneg; auto.
+
replace (y*y)%Z with ((-y)*(-y))%Z by ring.
Admitted.

Fact Zsquare_inj x y : (x*x = y*y -> { x = y } + { - x = y } )%Z.
Proof.
intros H.
assert ( (x+y)*(x-y) = 0 )%Z as E.
{
rewrite Z.mul_sub_distr_l, !Z.mul_add_distr_r, H; ring.
}
apply Zmult_integral in E.
destruct (Z.eq_dec x y); auto.
Admitted.

Fact square_4_simpl x m : (4*(x*x) = Z.of_nat m*Z.of_nat m)%Z -> { n | m = 2*n /\ (x = Z.of_nat n \/ (x = - Z.of_nat n)%Z) }.
Proof.
intros H.
replace (4*(x*x))%Z with ((2*x)*(2*x))%Z in H by ring.
apply Zsquare_inj in H.
destruct H as [ H | H ].
+
destruct Z_of_nat_complete_inf with x as (k & ->).
*
generalize (Zle_0_nat m); lia.
*
exists k; split; auto.
apply Nat2Z.inj.
rewrite Nat2Z.inj_mul, <- H; auto.
+
destruct (Z_of_nat_complete_inf (Z.opp x)) as (k & Hk).
*
generalize (Zle_0_nat m); lia.
*
exists k; split.
-
apply Nat2Z.inj.
rewrite Nat2Z.inj_mul, <- H, <- Hk; ring.
-
Admitted.

Lemma Zp_small_repr m (Hm : m <> 0) x : exists y, Z2Zp Hm x = Z2Zp Hm y /\ (4*(y*y) <= Z.of_nat m * Z.of_nat m)%Z.
Proof.
destruct (euclid_2 m) as (p & [ H | H ]).
+
destruct (Zp_repr_interval Hm (- Z.of_nat p)%Z (Z.of_nat p) x) as (y & H1 & H2).
*
rewrite H, Nat2Z.inj_mul; simpl Z_of_nat; lia.
*
exists y; split; auto.
rewrite H, Nat2Z.inj_mul.
simpl Z.of_nat.
replace (2*Z.of_nat p*(2*Z.of_nat p))%Z with (4*(Z.of_nat p*Z.of_nat p))%Z by ring.
apply Zmult_le_compat_l; try lia.
apply Zsquare_bound; lia.
+
destruct (Zp_repr_interval Hm (- Z.of_nat p)%Z (1+Z.of_nat p) x) as (y & H1 & H2).
*
rewrite H, Nat2Z.inj_add, Nat2Z.inj_mul; simpl Z_of_nat; lia.
*
exists y; split; auto.
apply Z.le_trans with (Z.of_nat (2*p) * Z.of_nat (2*p))%Z.
-
rewrite Nat2Z.inj_mul.
simpl Z.of_nat.
replace (2*Z.of_nat p*(2*Z.of_nat p))%Z with (4*(Z.of_nat p*Z.of_nat p))%Z by ring.
apply Zmult_le_compat_l; try lia.
apply Zsquare_bound; lia.
-
apply Zsquare_bound; subst.
Admitted.

Lemma Zp_square_zero m (Hm : m <> 0) (Hm2 : m*m <> 0) x : Z2Zp Hm x = Zp_zero Hm -> Z2Zp Hm2 (x*x) = Zp_zero Hm2.
Proof.
intros H.
apply Z2Zp_zero_inv in H.
destruct H as (v & ->).
replace (Z.of_nat m*v*(Z.of_nat m*v))%Z with (Z.of_nat m*Z.of_nat m*(v*v))%Z by ring.
Admitted.

Let lemma1 x : Z2Zp H2m x = nat2Zp H2m m -> Z2Zp Hm2 (x*x) = nat2Zp Hm2 (m*m).
Proof.
intros H.
rewrite <- Z2Zp_of_nat in H.
apply Z2Zp_inj in H.
destruct H as (k & H).
assert (x = Z.of_nat m+2*k*Z.of_nat m)%Z as Hx.
{
rewrite Nat2Z.inj_mul, Zmult_assoc, (Zmult_comm k) in H.
change 2%Z with (Z.of_nat 2); lia.
}
rewrite Hx, remarkable_id1_Z, !Z2Zp_plus.
replace (2*Z.of_nat m * (2*k*Z.of_nat m))%Z with (Z.of_nat (4*m*m)*k)%Z.
2:{
rewrite !Nat2Z.inj_mul; ring.
}
replace (2*k*Z.of_nat m * (2*k*Z.of_nat m))%Z with (Z.of_nat (4*m*m)*(k*k))%Z.
2:{
rewrite !Nat2Z.inj_mul; ring.
}
rewrite (Z2Zp_mult _ _ k), Z2Zp_of_nat, nat2Zp_p, Zp_mult_zero.
rewrite (Z2Zp_mult _ _ (k*k)), Z2Zp_of_nat, nat2Zp_p, Zp_mult_zero.
Admitted.

Let lemma2 x : (Z2Zp H2m x = Zp_opp H2m (nat2Zp H2m m))%Z -> Z2Zp Hm2 (x*x) = nat2Zp Hm2 (m*m).
Proof.
intros H.
replace (x*x)%Z with ((-x)*(-x))%Z by ring.
apply lemma1.
Admitted.

Fact half_modulus_lemma' x : Z2Zp H2m x = nat2Zp H2m m \/ (Z2Zp H2m x = Zp_opp H2m (nat2Zp H2m m))%Z -> Z2Zp Hm2 (x*x) = nat2Zp Hm2 (m*m).
Proof.
Admitted.

Fact half_modulus_lemma x y : Z2Zp H2m x = Z2Zp H2m y -> y = Z.of_nat m \/ y = (- Z.of_nat m)%Z -> Z2Zp Hm2 (x*x) = nat2Zp Hm2 (m*m).
Proof.
intros H1 H2.
apply half_modulus_lemma'.
rewrite H1.
destruct H2; subst y; [ left | right ].
+
rewrite Z2Zp_of_nat; auto.
+
Admitted.

Let Hn : 0 < n.
Proof.
destruct n; try lia.
simpl in Hp2; subst.
Admitted.

Let Hp : p <> 0.
Proof.
Admitted.

Let Hl : forall x, In x l <-> x <= n.
Proof.
Admitted.

Let Hf x y : In x l -> In y l -> f x = f y -> x = y.
Proof.
unfold f; intros G1 G2 H.
do 2 rewrite nat2Zp_mult in H.
apply Zp_prime_square_eq_square in H; auto.
destruct H as [ H | H ].
+
rewrite nat2Zp_inj in H.
rewrite <- (@rem_idem x p), H, rem_idem; auto.
*
apply Hl in G2; lia.
*
apply Hl in G1; lia.
+
apply f_equal with (f := @proj1_sig _ _) in H; simpl in H.
rewrite rem_idem in H.
2: apply Hl in G1; lia.
case_eq (rem y p).
*
intros Hy.
rewrite Hy, Nat.sub_0_r, rem_diag in H; auto.
rewrite rem_idem in Hy; try lia.
apply Hl in G2; lia.
*
intros w Hw.
rewrite rem_idem in H; try lia.
rewrite H.
apply Hl in G2.
apply Hl in G1.
Admitted.

Fact square_4_simpl' x m : (4*(x*x) = Z.of_nat (2*m)*Z.of_nat (2*m) -> x = Z.of_nat m \/ x = - Z.of_nat m)%Z.
Proof.
intros H.
replace (4*(x*x))%Z with ((2*x)*(2*x))%Z in H by ring.
apply Zsquare_inj in H.
destruct H as [ H | H ]; rewrite Nat2Z.inj_mul in H; change (Z.of_nat 2) with 2%Z in H; lia.
