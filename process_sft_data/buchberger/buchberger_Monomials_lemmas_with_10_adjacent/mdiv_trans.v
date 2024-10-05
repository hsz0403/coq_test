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

Lemma recomp_ok : forall (d : nat) (h : d <> 0) (m : mon d), recomp d h m = m.
intros d h m.
generalize h; clear h.
elim m.
intros h; elim h; auto.
Admitted.

Lemma proj_ok : forall (d : nat) (m : mon (S d)), c_n d (pmon1 (S d) m) (pmon2 (S d) m) = m.
intros d m; cut (S d <> 0); auto.
intros H; cut (recomp (S d) H m = m); auto.
Admitted.

Definition gen_mon : forall d : nat, nat -> mon d.
intros d; elim d.
intros n; exact n_0.
intros n H' n'; case n'.
exact (c_n n 1 (H' n)).
Admitted.

Definition mult_mon : forall d : nat, mon d -> mon d -> mon d.
intros d; elim d.
intros H' H'0; exact n_0.
intros n Rec S1 S2.
Admitted.

Theorem mult_mon_com : forall (d : nat) (a b : mon d), mult_mon d a b = mult_mon d b a.
intros d; elim d; simpl in |- *; auto.
intros n H' a b.
rewrite (H' (pmon2 (S n) a) (pmon2 (S n) b)); auto.
Admitted.

Theorem mult_mon_assoc : forall (d : nat) (a b c : mon d), mult_mon d a (mult_mon d b c) = mult_mon d (mult_mon d a b) c.
intros d; elim d; simpl in |- *; auto.
intros n H' a b c.
rewrite (H' (pmon2 (S n) a) (pmon2 (S n) b) (pmon2 (S n) c)); auto.
Admitted.

Definition zero_mon : forall d : nat, mon d.
intros d; elim d.
exact n_0.
Admitted.

Theorem mult_mon_zero_r : forall (d : nat) (a : mon d), mult_mon d a (zero_mon d) = a.
intros d a; elim a; auto.
simpl in |- *.
intros d0 n m H'; rewrite H'; auto.
Admitted.

Theorem mult_mon_zero_l : forall (d : nat) (a : mon d), mult_mon d (zero_mon d) a = a.
intros d a; elim a; auto.
simpl in |- *.
Admitted.

Lemma mdiv_proj : forall (d : nat) (m m' : mon (S d)), pmon1 (S d) m <= pmon1 (S d) m' -> mdiv d (pmon2 (S d) m) (pmon2 (S d) m') -> mdiv (S d) m m'.
Admitted.

Definition div_mon : forall d : nat, mon d -> mon d -> mon d.
intros d; elim d.
intros H' H'0; exact n_0.
intros n Rec S1 S2.
Admitted.

Theorem mdiv_div : forall (d : nat) (a b : mon d), mdiv d b a -> mult_mon d (div_mon d a b) b = a.
intros d a b H'; elim H'; simpl in |- *; auto.
intros d0 v v' n n' H'0 H'1 H'2.
rewrite (plus_comm (n' - n) n).
rewrite <- (le_plus_minus n n'); auto.
Admitted.

Definition div_mon_clean : forall d : nat, mon d -> mon d -> mon d * bool.
intros d; elim d.
intros H' H'0; exact (n_0, true).
intros n Rec S1 S2.
case (le_lt_dec (pmon1 (S n) S2) (pmon1 (S n) S1)).
case (Rec (pmon2 (S n) S1) (pmon2 (S n) S2)).
intros res b H'1; exact (c_n n (pmon1 (S n) S1 - pmon1 (S n) S2) res, b).
Admitted.

Definition is_nil : forall d : nat, mon d -> mon d.
intros d; case d.
intros H'; exact n_0.
Admitted.

Theorem is_nil_id : forall (d : nat) (a : mon d), a = is_nil d a.
Admitted.

Theorem mon_0 : forall a : mon 0, a = n_0.
Admitted.

Theorem eqmon_dec : forall (d : nat) (x y : mon d), {x = y} + {x <> y}.
intros d; elim d; auto.
intros x y; left.
rewrite (mon_0 x); rewrite (mon_0 y); auto.
intros n H' x y.
elim (eq_nat_dec (pmon1 (S n) x) (pmon1 (S n) y)); intros H'2.
elim (H' (pmon2 (S n) x) (pmon2 (S n) y)); intros H'3.
left.
rewrite <- (proj_ok n x).
rewrite <- (proj_ok n y).
rewrite H'3; rewrite H'2; auto.
right; rewrite <- (proj_ok n x); rewrite <- (proj_ok n y); red in |- *; intros H'0.
apply H'3.
change (pmon2 (S n) (c_n n (pmon1 (S n) x) (pmon2 (S n) x)) = pmon2 (S n) (c_n n (pmon1 (S n) y) (pmon2 (S n) y)) :> mon n) in |- *.
rewrite H'0; auto.
Admitted.

Theorem mult_div_com : forall (d : nat) (a b : mon d), div_mon d (mult_mon d a b) b = a.
intros d; elim d; simpl in |- *; auto.
intros n H' a b.
rewrite (H' (pmon2 (S n) a) (pmon2 (S n) b)); auto.
rewrite (plus_comm (pmon1 (S n) a) (pmon1 (S n) b)).
rewrite (minus_plus (pmon1 (S n) b) (pmon1 (S n) a)); auto.
Admitted.

Theorem mult_div_id : forall (d : nat) (a : mon d), div_mon d a a = zero_mon d.
intros d a; elim a; simpl in |- *; auto.
intros d0 n m H'; rewrite H'; auto.
Admitted.

Let gb : forall d : nat, mon d * bool -> bool.
Admitted.

Lemma mdiv_trans : forall d : nat, transitive (mon d) (mdiv d).
intros d; elim d; unfold transitive in |- *; auto.
intros x y z mdiv_xy; inversion mdiv_xy.
intros mdiv_yz; inversion mdiv_yz; auto.
rewrite <- (inj_pair2 nat (fun x : nat => mon x) 0 n_0 z); auto.
rewrite <- (inj_pair2 nat (fun x : nat => mon x) 0 n_0 x); auto.
intros n Rec x y z mdiv_xy; inversion mdiv_xy.
rewrite <- (inj_pair2 nat (fun x : nat => mon x) (S n) (c_n n n' v') y); auto.
rewrite <- (inj_pair2 nat (fun x : nat => mon x) (S n) (c_n n n0 v) x); auto.
intros mdiv_yz; inversion mdiv_yz; auto.
rewrite <- (inj_pair2 nat (fun x : nat => mon x) (S n) (c_n n n'0 v'0) z); auto.
apply mdiv_cons; auto.
apply le_trans with (m := n'); auto.
apply Rec with (y := v0); auto.
rewrite (inj_pair2 nat (fun x : nat => mon x) n v0 v'); auto.
