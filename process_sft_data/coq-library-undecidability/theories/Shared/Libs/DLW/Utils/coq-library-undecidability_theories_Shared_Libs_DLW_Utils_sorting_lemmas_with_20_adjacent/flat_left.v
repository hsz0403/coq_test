Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list sums php.
Set Implicit Arguments.
Local Notation "∑" := (msum plus 0).
Section nat_swap.
Variables (i j : nat).
Definition swap n := if eq_nat_dec n i then j else if eq_nat_dec n j then i else n.
Fact swap_spec_i : swap i = j.
Proof.
unfold swap; destruct (eq_nat_dec i i); auto; lia.
Fact swap_spec_j : swap j = i.
Proof.
unfold swap.
destruct (eq_nat_dec j i); auto.
destruct (eq_nat_dec j j); auto; lia.
Fact swap_spec n : n <> i -> n <> j -> swap n = n.
Proof.
unfold swap; intros.
destruct (eq_nat_dec n i); try lia.
destruct (eq_nat_dec n j); lia.
Fact swap_involutive n : swap (swap n) = n.
Proof.
destruct (eq_nat_dec n i).
{
subst n; rewrite swap_spec_i, swap_spec_j; auto.
}
destruct (eq_nat_dec n j).
{
subst n; rewrite swap_spec_j, swap_spec_i; auto.
}
{
do 2 (rewrite swap_spec; auto).
}
Fact swap_inj n m : swap n = swap m -> n = m.
Proof.
intros; rewrite <- (swap_involutive n), H.
apply swap_involutive.
End nat_swap.
Opaque swap.
Section php_fun.
Variable (n : nat) (f : nat -> nat) (Hf : forall i, i <= n -> f i < n).
End php_fun.
Section split_interval.
Variables (n i : nat) (Hi : i <= n).
Let g j := if le_lt_dec (S n) j then j else (* j > n *) if le_lt_dec i j then if le_lt_dec j i then n (* j = i *) else j-1 (* i < j <= n *) else j.
Let h j := if le_lt_dec (S n) j then j else (* j > n *) if le_lt_dec n j then i else (* j = n *) if le_lt_dec i j then j+1 (* i <= j < n *) else j.
Let Hg1 : forall j, j <= n -> g j <= n.
Proof.
intros j Hj; unfold g.
destruct (le_lt_dec (S n) j); try lia.
destruct (le_lt_dec i j); try lia.
destruct (le_lt_dec j i); lia.
Let Hg2 j : n < j -> g j = j.
Proof.
unfold g; destruct (le_lt_dec (S n) j); intros; lia.
Let Hh1 : forall j, j <= n -> h j <= n.
Proof.
intros j Hj; unfold h.
destruct (le_lt_dec (S n) j); try lia.
destruct (le_lt_dec n j); try lia.
destruct (le_lt_dec i j); lia.
Let Hh2 j : n < j -> h j = j.
Proof.
unfold h; destruct (le_lt_dec (S n) j); intros; lia.
Ltac mydestruct H := match goal with |- if ?c then _ else _ = _ => destruct c as [ H | H ]; try lia; auto end.
End split_interval.
Definition find_max_fun n f : { i | i <= n /\ forall j, j <= n -> f j <= f i }.
Proof.
revert f; induction n as [ | n IHn ]; intros f.
+
exists 0; split; auto.
intros [ | ]; auto; lia.
+
destruct (IHn f) as (i & H1 & H2).
destruct (le_lt_dec (f i) (f (S n))) as [ H | H ].
*
exists (S n); split; auto.
intros j Hj.
destruct (le_lt_dec j n) as [ H0 | H0 ].
-
apply le_trans with (2 := H); auto.
-
replace j with (S n); auto; lia.
*
exists i; split; auto.
intros j Hj.
destruct (le_lt_dec j n) as [ H0 | H0 ]; auto.
replace j with (S n); auto; lia.
Section sum_bounded_permutation.
Let sigma_sum_split i n f : i < n -> ∑ (S n) f = f i + f n + ∑ i f + ∑ (n-S i) (fun j => f (S i+j)).
Proof.
intros Hi.
replace (S n) with (i+1+(n- S i)+1) by lia.
repeat (rewrite msum_plus; auto).
do 2 rewrite msum_S, msum_0.
repeat rewrite <- plus_assoc.
rewrite (plus_comm).
repeat rewrite <- plus_assoc.
f_equal.
{
f_equal; lia.
}
simpl.
rewrite (plus_comm).
repeat rewrite <- plus_assoc.
f_equal.
{
f_equal; lia.
}
f_equal.
apply msum_ext.
intros; f_equal; lia.
Let sum_permutation_1 n i j g f : i < j < n -> g i = j -> g j = i -> (forall k, k <> i -> k <> j -> k < n -> g k = k) -> ∑ n f = ∑ n (fun i => f (g i)).
Proof.
revert i j g; induction n as [ | n IHn ]; intros i j g (H1 & H2) H3 H4 H5.
+
do 2 rewrite msum_0; auto.
+
destruct (eq_nat_dec j n) as [ H7 | H7 ].
*
rewrite H7 in *; clear j H7 H2.
do 2 rewrite sigma_sum_split with (1 := H1).
rewrite H3, H4; f_equal; [ f_equal | ]; try lia; apply msum_ext; intros; symmetry; f_equal; apply H5; lia.
*
do 2 (rewrite msum_plus1; auto); f_equal.
-
apply IHn with i j; auto; split; auto; lia.
-
symmetry; f_equal; apply H5; lia.
Inductive bounded_permut n (i j : nat) g : Prop := | in_nat_perm : i < n -> j < n -> g i = j -> g j = i -> (forall k, k <> i -> k <> j -> k < n -> g k = k) -> bounded_permut n i j g.
Hint Resolve swap_spec_i swap_spec_j swap_spec : core.
Fact swap_bounded_permut n i j : i < n -> j < n -> bounded_permut n i j (swap i j).
Proof.
constructor; auto.
Inductive composed_permutation n g : Prop := | in_cp_0 : (forall i, i < n -> g i = i) -> composed_permutation n g | in_cp_1 : forall i j f h, bounded_permut n i j f -> composed_permutation n h -> (forall i, i < n -> g i = h (f i)) -> composed_permutation n g.
Fact composed_permutation_ext n f g : (forall i, i < n -> f i = g i) -> composed_permutation n f -> composed_permutation n g.
Proof.
intros H1 H2; revert H2 g H1.
induction 1 as [ f Hg | f i j p q H1 H2 IH2 H3 ]; intros g H4.
+
constructor 1; intros; rewrite <- H4; auto.
+
constructor 2 with i j p q; auto.
intros; rewrite <- H4; auto.
Let flat n f i := if le_lt_dec n i then n else f i.
Let flat_left n f i : i < n -> flat n f i = f i.
Proof.
unfold flat; intro; destruct (le_lt_dec n i); auto; lia.
Let flat_right n f i : n <= i -> flat n f i = n.
Proof.
unfold flat; intro; destruct (le_lt_dec n i); auto; lia.
Fact composed_permutation_extends n f g : (forall i, i < n -> f i = g i) -> g n = n -> composed_permutation n f -> composed_permutation (S n) g.
Proof.
intros H1 H2 H3; revert H3 g H1 H2.
induction 1 as [ f Hg | f i j p q H1 H2 IH2 H3 ]; intros g H4 H5.
+
constructor 1; intros j Hj.
destruct (eq_nat_dec j n); subst; auto.
rewrite <- H4, Hg; auto; lia.
+
constructor 2 with i j (flat n p) (flat n q).
*
destruct H1 as [ G1 G2 G3 G4 G5 ]; constructor; try lia.
-
rewrite flat_left; auto; lia.
-
rewrite flat_left; auto; lia.
-
intros k ? ? ?.
destruct (eq_nat_dec k n); subst.
++
rewrite flat_right; auto.
++
rewrite flat_left, G5; lia.
*
apply IH2.
-
intros l Hl; rewrite flat_left; auto.
-
rewrite flat_right; lia.
*
intros k Hk.
destruct (eq_nat_dec k n); subst.
-
rewrite (flat_right p), flat_right; lia.
-
rewrite (flat_left p); try lia.
rewrite flat_left, <- H4; try lia.
++
apply H3; lia.
++
destruct H1 as [ G1 G2 G3 G4 G5 ].
destruct (eq_nat_dec k i).
{
subst; auto.
}
destruct (eq_nat_dec k j).
{
subst k; lia.
}
rewrite G5; lia.
Fact composed_permutation_S n g : g n = n -> composed_permutation n g -> composed_permutation (S n) g.
Proof.
intro; apply composed_permutation_extends; auto.
Inductive bounded_injective n f : Prop := | in_bounded_inj : (forall i, i < n -> f i < n) -> (forall i j, i < n -> j < n -> f i = f j -> i = j) -> bounded_injective n f.
Fact injective_composed_permutation n f : bounded_injective n f -> composed_permutation n f.
Proof.
intros [ H1 H2 ].
revert f H1 H2; induction n as [ | n IHn ]; intros f H1 H2.
+
constructor 1; intros; lia.
+
destruct (find_max_fun n f) as (i & H3 & H4).
destruct (le_lt_dec n (f i)) as [ C | C ].
-
assert (f i = n) as Hf1.
{
apply le_antisym; auto; apply le_S_n, H1; lia.
}
assert (forall j, j <= n -> j <> i -> f j < n) as Hf2.
{
intros j G1 G2.
destruct (eq_nat_dec (f j) n).
+
contradict G2; apply H2; lia.
+
specialize (H1 j); lia.
}
specialize (IHn (fun x => f (swap i n x))).
spec in IHn.
{
intros j Hj.
destruct (eq_nat_dec j i).
+
subst j; rewrite swap_spec_i; apply Hf2; lia.
+
rewrite swap_spec; try lia; apply Hf2; lia.
}
spec in IHn.
{
intros u v G1 G2 G3.
apply H2 in G3.
+
revert G3; apply swap_inj.
+
destruct (eq_nat_dec u i).
-
subst; rewrite swap_spec_i; lia.
-
rewrite swap_spec; lia.
+
destruct (eq_nat_dec v i).
-
subst; rewrite swap_spec_i; lia.
-
rewrite swap_spec; lia.
}
apply composed_permutation_S in IHn.
2: rewrite swap_spec_j, Hf1; auto.
generalize (@swap_bounded_permut (S n) i n); intros G.
do 2 (spec in G; try lia).
constructor 2 with (1 := G) (2 := IHn).
intros; rewrite swap_involutive; auto.
-
destruct (@php_fun n f) as (u & v & G1 & G2).
{
intros; apply le_lt_trans with (2 := C); auto.
}
apply H2 in G2; lia.
End sum_bounded_permutation.
Section sum_bijection.
Inductive bijection n g h : Type := | in_bij : (forall i, i < n -> g i < n) -> (forall i, i < n -> h i < n) -> (forall i, i < n -> g (h i) = i) -> (forall i, i < n -> h (g i) = i) -> bijection n g h.
Inductive triangle_bijection n k g h : Prop := | in_tb : (forall i j, j < i < n -> h (i,j) < k /\ g (h (i,j)) = (i,j)) -> (forall q, q < k -> snd (g q) < fst (g q) < n /\ h (g q) = q) -> triangle_bijection n k g h.
End sum_bijection.

Fact swap_spec_i : swap i = j.
Proof.
Admitted.

Fact swap_spec_j : swap j = i.
Proof.
unfold swap.
destruct (eq_nat_dec j i); auto.
Admitted.

Fact swap_spec n : n <> i -> n <> j -> swap n = n.
Proof.
unfold swap; intros.
destruct (eq_nat_dec n i); try lia.
Admitted.

Fact swap_involutive n : swap (swap n) = n.
Proof.
destruct (eq_nat_dec n i).
{
subst n; rewrite swap_spec_i, swap_spec_j; auto.
}
destruct (eq_nat_dec n j).
{
subst n; rewrite swap_spec_j, swap_spec_i; auto.
}
{
do 2 (rewrite swap_spec; auto).
Admitted.

Fact swap_inj n m : swap n = swap m -> n = m.
Proof.
intros; rewrite <- (swap_involutive n), H.
Admitted.

Theorem php_fun : exists i j, i < j <= n /\ f i = f j.
Proof.
destruct PHP_rel with (R := fun x y => y = f x) (l := list_an 0 (S n)) (m := list_an 0 n) as (a & i & b & j & c & v & H1 & H2 & H3 & H4).
+
intros x; rewrite list_an_spec; simpl; intros [ _ H ].
exists (f x); split; auto; rewrite list_an_spec; simpl; split; try lia.
apply Hf; lia.
+
do 2 rewrite list_an_length; auto.
+
exists i, j; split; try lia.
generalize H1; intros G1.
apply list_an_app_inv in G1.
destruct G1 as (G0 & G1); simpl in G1.
injection G1; clear G1; intros G1 G2.
symmetry in G1; apply list_an_app_inv in G1.
destruct G1 as (G3 & G1); simpl in G1.
injection G1; clear G1; intros G4 G1.
apply f_equal with (f := @length _) in H1.
revert H1; rew length; intros H1.
Admitted.

Let Hg1 : forall j, j <= n -> g j <= n.
Proof.
intros j Hj; unfold g.
destruct (le_lt_dec (S n) j); try lia.
destruct (le_lt_dec i j); try lia.
Admitted.

Let Hg2 j : n < j -> g j = j.
Proof.
Admitted.

Let Hh1 : forall j, j <= n -> h j <= n.
Proof.
intros j Hj; unfold h.
destruct (le_lt_dec (S n) j); try lia.
destruct (le_lt_dec n j); try lia.
Admitted.

Let Hh2 j : n < j -> h j = j.
Proof.
Admitted.

Theorem split_interval : { g : nat -> nat & { h | (forall j, j <= n -> g j <= n) /\ (forall j, j <= n -> h j <= n) /\ (forall j, g (h j) = j) /\ (forall j, h (g j) = j) /\ g i = n } }.
Proof.
exists g, h.
split; [ | split; [ | split; [ | split ] ] ]; auto.
+
intros j; unfold h.
destruct (le_lt_dec (S n) j) as [ | H1 ]; auto.
destruct (le_lt_dec n j) as [ H2 | H2 ].
{
unfold g.
destruct (le_lt_dec (S n) i); try lia.
destruct (le_lt_dec i i); lia.
}
destruct (le_lt_dec i j) as [ H3 | H3 ].
{
unfold g.
destruct (le_lt_dec (S n) (j+1)); try lia.
destruct (le_lt_dec i (j+1)); try lia.
destruct (le_lt_dec (j+1) i); lia.
}
{
unfold g.
destruct (le_lt_dec (S n) j); try lia.
destruct (le_lt_dec i j); try lia.
}
+
intros j; unfold g.
destruct (le_lt_dec (S n) j) as [ | H1 ]; auto.
destruct (le_lt_dec i j) as [ H2 | H2 ].
destruct (le_lt_dec j i) as [ H3 | H3 ].
{
unfold h.
destruct (le_lt_dec (S n) n); try lia.
destruct (le_lt_dec n n); lia.
}
{
unfold h.
destruct (le_lt_dec (S n) (j-1)); try lia.
destruct (le_lt_dec n (j-1)); try lia.
destruct (le_lt_dec i (j-1)); lia.
}
{
unfold h.
destruct (le_lt_dec (S n) j); try lia.
destruct (le_lt_dec n j); try lia.
destruct (le_lt_dec i j); lia.
}
+
unfold g.
destruct (le_lt_dec (S n) i); try lia.
Admitted.

Definition find_max_fun n f : { i | i <= n /\ forall j, j <= n -> f j <= f i }.
Proof.
revert f; induction n as [ | n IHn ]; intros f.
+
exists 0; split; auto.
intros [ | ]; auto; lia.
+
destruct (IHn f) as (i & H1 & H2).
destruct (le_lt_dec (f i) (f (S n))) as [ H | H ].
*
exists (S n); split; auto.
intros j Hj.
destruct (le_lt_dec j n) as [ H0 | H0 ].
-
apply le_trans with (2 := H); auto.
-
replace j with (S n); auto; lia.
*
exists i; split; auto.
intros j Hj.
destruct (le_lt_dec j n) as [ H0 | H0 ]; auto.
Admitted.

Let sigma_sum_split i n f : i < n -> ∑ (S n) f = f i + f n + ∑ i f + ∑ (n-S i) (fun j => f (S i+j)).
Proof.
intros Hi.
replace (S n) with (i+1+(n- S i)+1) by lia.
repeat (rewrite msum_plus; auto).
do 2 rewrite msum_S, msum_0.
repeat rewrite <- plus_assoc.
rewrite (plus_comm).
repeat rewrite <- plus_assoc.
f_equal.
{
f_equal; lia.
}
simpl.
rewrite (plus_comm).
repeat rewrite <- plus_assoc.
f_equal.
{
f_equal; lia.
}
f_equal.
apply msum_ext.
Admitted.

Let sum_permutation_1 n i j g f : i < j < n -> g i = j -> g j = i -> (forall k, k <> i -> k <> j -> k < n -> g k = k) -> ∑ n f = ∑ n (fun i => f (g i)).
Proof.
revert i j g; induction n as [ | n IHn ]; intros i j g (H1 & H2) H3 H4 H5.
+
do 2 rewrite msum_0; auto.
+
destruct (eq_nat_dec j n) as [ H7 | H7 ].
*
rewrite H7 in *; clear j H7 H2.
do 2 rewrite sigma_sum_split with (1 := H1).
rewrite H3, H4; f_equal; [ f_equal | ]; try lia; apply msum_ext; intros; symmetry; f_equal; apply H5; lia.
*
do 2 (rewrite msum_plus1; auto); f_equal.
-
apply IHn with i j; auto; split; auto; lia.
-
Admitted.

Fact swap_bounded_permut n i j : i < n -> j < n -> bounded_permut n i j (swap i j).
Proof.
Admitted.

Fact composed_permutation_ext n f g : (forall i, i < n -> f i = g i) -> composed_permutation n f -> composed_permutation n g.
Proof.
intros H1 H2; revert H2 g H1.
induction 1 as [ f Hg | f i j p q H1 H2 IH2 H3 ]; intros g H4.
+
constructor 1; intros; rewrite <- H4; auto.
+
constructor 2 with i j p q; auto.
Admitted.

Let flat_right n f i : n <= i -> flat n f i = n.
Proof.
Admitted.

Fact composed_permutation_extends n f g : (forall i, i < n -> f i = g i) -> g n = n -> composed_permutation n f -> composed_permutation (S n) g.
Proof.
intros H1 H2 H3; revert H3 g H1 H2.
induction 1 as [ f Hg | f i j p q H1 H2 IH2 H3 ]; intros g H4 H5.
+
constructor 1; intros j Hj.
destruct (eq_nat_dec j n); subst; auto.
rewrite <- H4, Hg; auto; lia.
+
constructor 2 with i j (flat n p) (flat n q).
*
destruct H1 as [ G1 G2 G3 G4 G5 ]; constructor; try lia.
-
rewrite flat_left; auto; lia.
-
rewrite flat_left; auto; lia.
-
intros k ? ? ?.
destruct (eq_nat_dec k n); subst.
++
rewrite flat_right; auto.
++
rewrite flat_left, G5; lia.
*
apply IH2.
-
intros l Hl; rewrite flat_left; auto.
-
rewrite flat_right; lia.
*
intros k Hk.
destruct (eq_nat_dec k n); subst.
-
rewrite (flat_right p), flat_right; lia.
-
rewrite (flat_left p); try lia.
rewrite flat_left, <- H4; try lia.
++
apply H3; lia.
++
destruct H1 as [ G1 G2 G3 G4 G5 ].
destruct (eq_nat_dec k i).
{
subst; auto.
}
destruct (eq_nat_dec k j).
{
subst k; lia.
}
Admitted.

Fact composed_permutation_S n g : g n = n -> composed_permutation n g -> composed_permutation (S n) g.
Proof.
Admitted.

Fact injective_composed_permutation n f : bounded_injective n f -> composed_permutation n f.
Proof.
intros [ H1 H2 ].
revert f H1 H2; induction n as [ | n IHn ]; intros f H1 H2.
+
constructor 1; intros; lia.
+
destruct (find_max_fun n f) as (i & H3 & H4).
destruct (le_lt_dec n (f i)) as [ C | C ].
-
assert (f i = n) as Hf1.
{
apply le_antisym; auto; apply le_S_n, H1; lia.
}
assert (forall j, j <= n -> j <> i -> f j < n) as Hf2.
{
intros j G1 G2.
destruct (eq_nat_dec (f j) n).
+
contradict G2; apply H2; lia.
+
specialize (H1 j); lia.
}
specialize (IHn (fun x => f (swap i n x))).
spec in IHn.
{
intros j Hj.
destruct (eq_nat_dec j i).
+
subst j; rewrite swap_spec_i; apply Hf2; lia.
+
rewrite swap_spec; try lia; apply Hf2; lia.
}
spec in IHn.
{
intros u v G1 G2 G3.
apply H2 in G3.
+
revert G3; apply swap_inj.
+
destruct (eq_nat_dec u i).
-
subst; rewrite swap_spec_i; lia.
-
rewrite swap_spec; lia.
+
destruct (eq_nat_dec v i).
-
subst; rewrite swap_spec_i; lia.
-
rewrite swap_spec; lia.
}
apply composed_permutation_S in IHn.
2: rewrite swap_spec_j, Hf1; auto.
generalize (@swap_bounded_permut (S n) i n); intros G.
do 2 (spec in G; try lia).
constructor 2 with (1 := G) (2 := IHn).
intros; rewrite swap_involutive; auto.
-
destruct (@php_fun n f) as (u & v & G1 & G2).
{
intros; apply le_lt_trans with (2 := C); auto.
}
Admitted.

Theorem sum_bounded_permutation n i j g f : bounded_permut n i j g -> ∑ n f = ∑ n (fun i => f (g i)).
Proof.
intros [ H1 H2 H3 H4 H5 ].
destruct (lt_eq_lt_dec i j) as [ [ G1 | G1 ] | G1 ].
+
apply sum_permutation_1 with i j; auto; split; auto.
+
apply msum_ext; rewrite <- G1 in *; clear j G1.
intros j Hj; f_equal.
destruct (eq_nat_dec j i); subst; auto.
rewrite H5; auto.
+
Admitted.

Theorem sum_composed_permutation n f g : composed_permutation n g -> ∑ n f = ∑ n (fun i => f (g i)).
Proof.
induction 1 as [ g Hg | g i j p q H1 H2 IH2 H3 ].
+
symmetry; apply msum_ext; intros; f_equal; apply Hg; auto.
+
rewrite IH2, sum_bounded_permutation with (1 := H1).
Admitted.

Theorem sum_injective n f g : bounded_injective n g -> ∑ n f = ∑ n (fun i => f (g i)).
Proof.
Admitted.

Theorem sum_bijection n f g h : bijection n g h -> ∑ n f = ∑ n (fun i => f (g i)).
Proof.
intros [ H1 H2 H3 H4 ].
apply sum_injective.
constructor; auto.
Admitted.

Let flat_left n f i : i < n -> flat n f i = f i.
Proof.
unfold flat; intro; destruct (le_lt_dec n i); auto; lia.
