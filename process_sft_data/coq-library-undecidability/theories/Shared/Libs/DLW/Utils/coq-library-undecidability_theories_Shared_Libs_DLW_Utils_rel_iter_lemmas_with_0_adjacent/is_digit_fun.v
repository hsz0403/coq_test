Require Import Arith Nat Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac gcd prime binomial sums.
Set Implicit Arguments.
Section rel_iter.
Variable (X : Type) (R : X -> X -> Prop).
Fixpoint rel_iter n := match n with | 0 => eq | S n => fun x z => exists y, R x y /\ rel_iter n y z end.
Fact rel_iter_plus n m x y : rel_iter (n+m) x y <-> exists a, rel_iter n x a /\ rel_iter m a y.
Proof.
revert x y; induction n as [ | n IHn ]; intros x y; simpl.
+
split.
*
exists x; split; auto.
*
intros (? & ? & ?); subst; auto.
+
split.
*
intros (a & H1 & H2).
apply IHn in H2.
destruct H2 as (b & H2 & H3).
exists b; split; auto; exists a; auto.
*
intros (a & (b & H1 & H2) & H3).
exists b; split; auto.
apply IHn; exists a; auto.
Fact rel_iter_1 x y : rel_iter 1 x y <-> R x y.
Proof.
simpl; split.
*
intros (? & ? & ?); subst; auto.
*
exists y; auto.
Fact rel_iter_S n x y : rel_iter (S n) x y <-> exists a, rel_iter n x a /\ R a y.
Proof.
replace (S n) with (n+1) by lia.
rewrite rel_iter_plus.
split; intros (a & H1 & H2); exists a; revert H1 H2; rewrite rel_iter_1; auto.
Fact rel_iter_sequence n x y : rel_iter n x y <-> exists f, f 0 = x /\ f n = y /\ forall i, i < n -> R (f i) (f (S i)).
Proof.
split.
*
revert x y; induction n as [ | n IHn ]; simpl; intros x y.
+
intros; subst y; exists (fun _ => x); repeat split; auto; intros; lia.
+
intros (a & H1 & H2).
destruct IHn with (1 := H2) as (f & H3 & H4 & H5).
exists (fun i => match i with 0 => x | S i => f i end); repeat split; auto.
intros [ | i ] Hi; subst; auto.
apply H5; lia.
*
intros (f & H1 & H2 & H3); subst x y.
induction n as [ | n IHn ].
+
simpl; auto.
+
rewrite rel_iter_S.
exists (f n); split; auto.
End rel_iter.
Local Notation power := (mscal mult 1).
Definition is_digit c q i y := y < q /\ exists a b, c = (a*q+y)*power i q+b /\ b < power i q.
Fact is_digit_fun c q i x y : is_digit c q i x -> is_digit c q i y -> x = y.
Proof.
intros (H1 & a1 & b1 & H3 & H4) (H2 & a2 & b2 & H5 & H6).
rewrite H3 in H5.
apply div_rem_uniq, proj1 in H5; auto; try lia.
apply div_rem_uniq, proj2 in H5; auto; lia.
Definition is_seq (R : nat -> nat -> Prop) c q n := forall i, i < n -> exists y y', is_digit c q i y /\ is_digit c q (1+i) y' /\ R y y'.
Section rel_iter_bound.
Variable (R : nat -> nat -> Prop) (k : nat) (Hk1 : forall x y, R x y -> y <= k*x).
Let Hk' : forall x y, R x y -> y <= (S k)*x.
Proof.
intros x y H; apply le_trans with (1 := Hk1 H), mult_le_compat_r; lia.
Definition rel_iter_bound n x y := exists q c, x*power n (S k) < q /\ is_seq R c q n /\ is_digit c q 0 x /\ is_digit c q n y.
Notation power := (mscal mult 1).
Notation "∑" := (msum plus 0).
Hint Resolve rel_iter_bound_iter rel_iter_iter_bound : core.
End rel_iter_bound.
Section rel_iter_seq.
Variable (R : nat -> nat -> Prop).
Definition rel_iter_seq n x y := exists q c, is_seq R c q n /\ is_digit c q 0 x /\ is_digit c q n y.
Notation power := (mscal mult 1).
Notation "∑" := (msum plus 0).
Hint Resolve rel_iter_seq_iter rel_iter_iter_seq : core.
End rel_iter_seq.

Fact is_digit_fun c q i x y : is_digit c q i x -> is_digit c q i y -> x = y.
Proof.
intros (H1 & a1 & b1 & H3 & H4) (H2 & a2 & b2 & H5 & H6).
rewrite H3 in H5.
apply div_rem_uniq, proj1 in H5; auto; try lia.
apply div_rem_uniq, proj2 in H5; auto; lia.
