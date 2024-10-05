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

Theorem mult_mon_zero_l : forall (d : nat) (a : mon d), mult_mon d (zero_mon d) a = a.
intros d a; elim a; auto.
simpl in |- *.
intros d0 n m H'; rewrite H'; auto.
