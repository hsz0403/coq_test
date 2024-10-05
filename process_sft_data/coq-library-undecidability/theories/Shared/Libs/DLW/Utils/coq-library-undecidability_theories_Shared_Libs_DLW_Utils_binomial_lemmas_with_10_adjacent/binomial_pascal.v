Require Import Arith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac gcd.
Set Implicit Arguments.
Section factorial.
Fixpoint fact n := match n with 0 => 1 | S n => (S n) * fact n end.
Fact fact_0 : fact 0 = 1.
Proof.
trivial.
Fact fact_S n : fact (S n) = (S n)*fact n.
Proof.
trivial.
Fact fact_gt_0 n : 0 < fact n.
Proof.
unfold lt; simpl.
induction n as [ | n IHn ]; simpl; auto.
generalize (n*fact n); intros; lia.
Fact divides_n_fact_n n : 0 < n -> divides n (fact n).
Proof.
destruct n as [ | n ]; try lia; intros _.
apply divides_mult_r, divides_refl.
Fact divides_fact_S n : divides (fact n) (fact (S n)).
Proof.
apply divides_mult, divides_refl.
Fact divides_fact n i : 0 < i <= n -> divides i (fact n).
Proof.
intros (H1 & H2); revert H2.
induction 1 as [ | n H2 IH2 ].
+
apply divides_n_fact_n; auto.
+
apply divides_trans with (1 := IH2), divides_fact_S.
End factorial.
Section binomial.
Infix "<d" := divides (at level 70, no associativity).
Hint Resolve divides_refl : core.
Let fact_neq_0 n : fact n <> 0.
Proof.
generalize (fact_gt_0 n); lia.
Fixpoint binomial n p := match n, p with | _, 0 => 1 | 0, S _ => 0 | S n, S p => binomial n p + binomial n (S p) end.
Fact binomial_n0 n : binomial n 0 = 1.
Proof.
destruct n; auto.
Fact binomial_SS n p : binomial (S n) (S p) = binomial n p + binomial n (S p).
Proof.
auto.
Fact binomial_n1 n : 1 <= n -> binomial n 1 = n.
Proof.
destruct n as [ | n ]; try lia; intros _.
induction n as [ | n IHn ]; auto.
rewrite binomial_SS, IHn, binomial_n0; lia.
Fact binomial_gt n : forall p, n < p -> binomial n p = 0.
Proof.
induction n as [ | n IHn ]; intros [|] ?; simpl; auto; try lia.
do 2 (rewrite IHn; try lia).
Fact binomial_nn n : binomial n n = 1.
Proof.
induction n; auto; rewrite binomial_SS, binomial_gt with (p := S _); lia.
Fact binomial_le n p : p <= n -> binomial n p = div (fact n) (fact p * fact (n-p)).
Proof.
intros H.
symmetry; apply div_prop with (r := 0).
+
rewrite binomial_thm with (p := p); auto; ring.
+
red; change 1 with (1*1); apply mult_le_compat; apply fact_gt_0.
Fact binomial_sym n p : p <= n -> binomial n p = binomial n (n-p).
Proof.
intros H; do 2 (rewrite binomial_le; try lia).
rewrite mult_comm; do 3 f_equal; lia.
Fact binomial_spec n p : p <= n -> fact n = binomial n p * fact p * fact (n-p).
Proof.
apply binomial_thm.
Fact binomial_0n n : 0 < n -> binomial 0 n = 0.
Proof.
intros; rewrite binomial_gt; auto; simpl.
End binomial.

Fact binomial_n0 n : binomial n 0 = 1.
Proof.
Admitted.

Fact binomial_SS n p : binomial (S n) (S p) = binomial n p + binomial n (S p).
Proof.
Admitted.

Fact binomial_n1 n : 1 <= n -> binomial n 1 = n.
Proof.
destruct n as [ | n ]; try lia; intros _.
induction n as [ | n IHn ]; auto.
Admitted.

Fact binomial_gt n : forall p, n < p -> binomial n p = 0.
Proof.
induction n as [ | n IHn ]; intros [|] ?; simpl; auto; try lia.
Admitted.

Fact binomial_nn n : binomial n n = 1.
Proof.
Admitted.

Theorem binomial_thm n p : p <= n -> fact n = binomial n p * fact p * fact (n-p).
Proof.
intros H.
replace n with (n-p+p) at 1 2 by lia.
generalize (n-p); clear n H; intros n.
induction on n p as IH with measure (n+p).
revert n p IH; intros [ | n ] [ | p ] IH; simpl plus; auto.
+
rewrite binomial_nn; simpl; lia.
+
rewrite Nat.add_0_r, binomial_n0; simpl; lia.
+
rewrite fact_S, binomial_SS.
replace (S (n+S p)) with (S p+S n) by lia.
do 3 rewrite Nat.mul_add_distr_r; f_equal.
*
replace (n+S p) with (S n+p) by lia.
rewrite fact_S, IH; try lia; ring.
*
Admitted.

Fact binomial_le n p : p <= n -> binomial n p = div (fact n) (fact p * fact (n-p)).
Proof.
intros H.
symmetry; apply div_prop with (r := 0).
+
rewrite binomial_thm with (p := p); auto; ring.
+
Admitted.

Fact binomial_sym n p : p <= n -> binomial n p = binomial n (n-p).
Proof.
intros H; do 2 (rewrite binomial_le; try lia).
Admitted.

Fact binomial_spec n p : p <= n -> fact n = binomial n p * fact p * fact (n-p).
Proof.
Admitted.

Fact binomial_0n n : 0 < n -> binomial 0 n = 0.
Proof.
Admitted.

Theorem binomial_pascal n p : binomial (S n) (S p) = binomial n p + binomial n (S p).
Proof.
auto.
