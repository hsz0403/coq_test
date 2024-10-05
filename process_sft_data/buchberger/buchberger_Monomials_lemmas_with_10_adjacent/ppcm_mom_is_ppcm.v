Require Import Arith.
Require Import Compare.
Require Import Compare_dec.
Require Import Peano_dec.
Require Import Relation_Definitions.
Require Import Eqdep.
Require Import Max.
Section Monomials.
Inductive mon : nat -> Set := | n_0 : mon 0 | c_n : forall d : nat, nat -> mon d -> mon (S d).
Definition pmon1 : forall d : nat, mon d -> nat.
intros d m; case m.
exact 0.
intros d' n p; exact n.
Defined.
Definition pmon2 : forall d : nat, mon d -> mon (pred d).
intros d m; case m.
exact n_0.
intros d' n p; exact p.
Defined.
Definition recomp : forall d : nat, d <> 0 -> mon d -> mon d.
intros d; case d.
intros H'; apply False_rec; case H'; auto.
intros d' H m; exact (c_n d' (pmon1 (S d') m) (pmon2 (S d') m)).
Defined.
Definition gen_mon : forall d : nat, nat -> mon d.
intros d; elim d.
intros n; exact n_0.
intros n H' n'; case n'.
exact (c_n n 1 (H' n)).
intros n''; exact (c_n n 0 (H' n'')).
Defined.
Definition mult_mon : forall d : nat, mon d -> mon d -> mon d.
intros d; elim d.
intros H' H'0; exact n_0.
intros n Rec S1 S2.
exact (c_n n (pmon1 (S n) S1 + pmon1 (S n) S2) (Rec (pmon2 (S n) S1) (pmon2 (S n) S2))).
Defined.
Definition zero_mon : forall d : nat, mon d.
intros d; elim d.
exact n_0.
intros n Rec; exact (c_n n 0 Rec).
Defined.
Inductive mdiv : forall d : nat, mon d -> mon d -> Prop := | mdiv_nil : mdiv 0 n_0 n_0 | mdiv_cons : forall (d : nat) (v v' : mon d) (n n' : nat), n <= n' -> mdiv d v v' -> mdiv (S d) (c_n d n v) (c_n d n' v').
Hint Resolve mdiv_nil mdiv_cons : core.
Definition div_mon : forall d : nat, mon d -> mon d -> mon d.
intros d; elim d.
intros H' H'0; exact n_0.
intros n Rec S1 S2.
exact (c_n n (pmon1 (S n) S1 - pmon1 (S n) S2) (Rec (pmon2 (S n) S1) (pmon2 (S n) S2))).
Defined.
Definition div_mon_clean : forall d : nat, mon d -> mon d -> mon d * bool.
intros d; elim d.
intros H' H'0; exact (n_0, true).
intros n Rec S1 S2.
case (le_lt_dec (pmon1 (S n) S2) (pmon1 (S n) S1)).
case (Rec (pmon2 (S n) S1) (pmon2 (S n) S2)).
intros res b H'1; exact (c_n n (pmon1 (S n) S1 - pmon1 (S n) S2) res, b).
intros H'; exact (S1, false).
Defined.
Definition is_nil : forall d : nat, mon d -> mon d.
intros d; case d.
intros H'; exact n_0.
intros n H'; exact H'.
Defined.
Hint Resolve mon_0 : core.
Let gb : forall d : nat, mon d * bool -> bool.
intros d H'; case H'; auto.
Defined.
Let gm : forall d : nat, mon d * bool -> mon d.
intros d H'; case H'; auto.
Defined.
Definition ppcm_mon : forall d : nat, mon d -> mon d -> mon d.
intros d; elim d.
intros m1 m2; exact n_0.
intros n Rec S1 S2.
exact (c_n n (max (pmon1 (S n) S1) (pmon1 (S n) S2)) (Rec (pmon2 (S n) S1) (pmon2 (S n) S2))).
Defined.
End Monomials.

Let gb : forall d : nat, mon d * bool -> bool.
Admitted.

Let gm : forall d : nat, mon d * bool -> mon d.
Admitted.

Theorem minus_lt_0 : forall m n : nat, n < m -> n - m = 0.
intros m; elim m; simpl in |- *; auto.
intros n H; absurd (n < 0); auto with arith.
Admitted.

Theorem div_clean_dec2 : forall (d : nat) (a b : mon d), gb d (div_mon_clean d a b) = false -> mult_mon d (div_mon d a b) b <> a.
intros d; elim d; simpl in |- *; auto.
intros a H' H'0; inversion H'0; auto.
intros n H' a b.
case (le_lt_dec (pmon1 (S n) b) (pmon1 (S n) a)); simpl in |- *; auto.
intros l; generalize (H' (pmon2 (S n) a) (pmon2 (S n) b)).
case (div_mon_clean n (pmon2 (S n) a) (pmon2 (S n) b)); simpl in |- *; auto.
intros H'0 b0 H'1 H'2; red in |- *; intros H'3.
lapply H'1; [ intros H'4; apply H'4; clear H'1 | clear H'1 ]; auto.
change (pmon2 (S n) (c_n n (pmon1 (S n) a - pmon1 (S n) b + pmon1 (S n) b) (mult_mon n (div_mon n (pmon2 (S n) a) (pmon2 (S n) b)) (pmon2 (S n) b))) = pmon2 (S n) a :>mon n) in |- *.
rewrite H'3; auto.
intros H'0 H'1; red in |- *; intros H'2; absurd (pmon1 (S n) a - pmon1 (S n) b + pmon1 (S n) b = pmon1 (S n) a); auto.
2: change (pmon1 (S n) (c_n n (pmon1 (S n) a - pmon1 (S n) b + pmon1 (S n) b) (mult_mon n (div_mon n (pmon2 (S n) a) (pmon2 (S n) b)) (pmon2 (S n) b))) = pmon1 (S n) a :>nat) in |- *.
2: rewrite H'2; auto.
rewrite (minus_lt_0 (pmon1 (S n) b) (pmon1 (S n) a)); simpl in |- *; auto.
red in |- *; intros H'3; absurd (pmon1 (S n) a < pmon1 (S n) b); auto.
apply le_not_lt; auto.
Admitted.

Theorem div_clean_dec1 : forall (d : nat) (a b : mon d), gb d (div_mon_clean d a b) = true -> gm d (div_mon_clean d a b) = div_mon d a b /\ mult_mon d (div_mon d a b) b = a.
intros d; elim d; simpl in |- *; auto.
intros n H' a b; case (le_lt_dec (pmon1 (S n) b) (pmon1 (S n) a)); simpl in |- *; auto.
2: intros H'0 H'1; inversion H'1.
intros l; generalize (H' (pmon2 (S n) a) (pmon2 (S n) b)).
case (div_mon_clean n (pmon2 (S n) a) (pmon2 (S n) b)); simpl in |- *; auto.
intros m b' H1 H2.
case (H1 H2); intros H3 H4; split; auto.
rewrite H3; auto.
rewrite (plus_comm (pmon1 (S n) a - pmon1 (S n) b) (pmon1 (S n) b)).
rewrite <- (le_plus_minus (pmon1 (S n) b) (pmon1 (S n) a)); auto.
rewrite H4; auto.
Admitted.

Definition ppcm_mon : forall d : nat, mon d -> mon d -> mon d.
intros d; elim d.
intros m1 m2; exact n_0.
intros n Rec S1 S2.
Admitted.

Theorem ppcm_com : forall (d : nat) (a b : mon d), ppcm_mon d a b = ppcm_mon d b a.
intros d; elim d; simpl in |- *; auto.
intros n H' a b; rewrite (H' (pmon2 (S n) a) (pmon2 (S n) b)).
Admitted.

Theorem ppcm_prop_l : forall (d : nat) (a b : mon d), ppcm_mon d a b = mult_mon d (div_mon d (ppcm_mon d a b) a) a.
intros d; elim d; simpl in |- *; auto.
intros n H' a b; pattern (ppcm_mon n (pmon2 (S n) a) (pmon2 (S n) b)) at 1 in |- *; rewrite (H' (pmon2 (S n) a) (pmon2 (S n) b)).
pattern (max (pmon1 (S n) a) (pmon1 (S n) b)) at 1 in |- *; rewrite (le_plus_minus (pmon1 (S n) a) (max (pmon1 (S n) a) (pmon1 (S n) b))) ; auto.
rewrite (plus_comm (pmon1 (S n) a) (max (pmon1 (S n) a) (pmon1 (S n) b) - pmon1 (S n) a)) ; auto.
Admitted.

Theorem ppcm_prop_r : forall (d : nat) (a b : mon d), ppcm_mon d a b = mult_mon d (div_mon d (ppcm_mon d a b) b) b.
intros d; elim d; simpl in |- *; auto.
intros n H' a b; pattern (ppcm_mon n (pmon2 (S n) a) (pmon2 (S n) b)) at 1 in |- *; rewrite (H' (pmon2 (S n) a) (pmon2 (S n) b)).
pattern (max (pmon1 (S n) a) (pmon1 (S n) b)) at 1 in |- *; rewrite (le_plus_minus (pmon1 (S n) b) (max (pmon1 (S n) a) (pmon1 (S n) b))) ; auto.
rewrite (plus_comm (pmon1 (S n) b) (max (pmon1 (S n) a) (pmon1 (S n) b) - pmon1 (S n) b)) ; auto.
Admitted.

Theorem plus_minus_le : forall a b : nat, a - b + b = a -> b <= a.
intros a; elim a; simpl in |- *; auto.
intros b H'; rewrite H'; auto.
intros n H' b; case b; simpl in |- *; auto with arith.
intros n0; rewrite (plus_comm (n - n0) (S n0)); simpl in |- *; auto.
Admitted.

Theorem ppcm_mom_is_ppcm : forall (d : nat) (a b c : mon d), c = mult_mon d (div_mon d c a) a -> c = mult_mon d (div_mon d c b) b -> c = mult_mon d (div_mon d c (ppcm_mon d a b)) (ppcm_mon d a b).
intros d; elim d; simpl in |- *; auto.
intros n H' a b c H'0 H'1.
rewrite <- (H' (pmon2 (S n) a) (pmon2 (S n) b) (pmon2 (S n) c)); auto.
2: change (pmon2 (S n) c = pmon2 (S n) (c_n n (pmon1 (S n) c - pmon1 (S n) a + pmon1 (S n) a) (mult_mon n (div_mon n (pmon2 (S n) c) (pmon2 (S n) a)) (pmon2 (S n) a))) :>mon n) in |- *; auto.
2: rewrite <- H'0; auto.
2: change (pmon2 (S n) c = pmon2 (S n) (c_n n (pmon1 (S n) c - pmon1 (S n) b + pmon1 (S n) b) (mult_mon n (div_mon n (pmon2 (S n) c) (pmon2 (S n) b)) (pmon2 (S n) b))) :>mon n) in |- *; auto.
2: rewrite <- H'1; auto.
rewrite (plus_comm (pmon1 (S n) c - max (pmon1 (S n) a) (pmon1 (S n) b)) (max (pmon1 (S n) a) (pmon1 (S n) b))).
rewrite <- (le_plus_minus (max (pmon1 (S n) a) (pmon1 (S n) b)) (pmon1 (S n) c)) ; auto.
rewrite <- (proj_ok n c); auto.
apply max_case2; auto.
apply plus_minus_le; auto.
change (pmon1 (S n) (c_n n (pmon1 (S n) c - pmon1 (S n) a + pmon1 (S n) a) (mult_mon n (div_mon n (pmon2 (S n) c) (pmon2 (S n) a)) (pmon2 (S n) a))) = pmon1 (S n) c :>nat) in |- *; auto.
rewrite <- H'0; auto.
apply plus_minus_le; auto.
change (pmon1 (S n) (c_n n (pmon1 (S n) c - pmon1 (S n) b + pmon1 (S n) b) (mult_mon n (div_mon n (pmon2 (S n) c) (pmon2 (S n) b)) (pmon2 (S n) b))) = pmon1 (S n) c :>nat) in |- *; auto.
rewrite <- H'1; auto.
