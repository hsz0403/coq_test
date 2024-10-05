Require Import Eqdep.
Require Import Arith.
Require Import Compare_dec.
Require Import Monomials.
Require Import LetP.
Section lexi_order.
Inductive orderc : forall n : nat, mon n -> mon n -> Prop := | lo1 : forall (n a b : nat) (p : mon n), b < a -> orderc (S n) (c_n n a p) (c_n n b p) | lo2 : forall (n a b : nat) (p q : mon n), orderc n p q -> orderc (S n) (c_n n a p) (c_n n b q).
Hint Resolve lo1 lo2 : core.
Definition degc : forall n : nat, mon n -> nat.
intros n H'; elim H'.
exact 0.
intros d n1 M n2; exact (n1 + n2).
Defined.
Inductive total_orderc : forall n : nat, mon n -> mon n -> Prop := | total_orderc0 : forall (n : nat) (p q : mon n), degc n p < degc n q -> total_orderc n p q | total_orderc1 : forall (n : nat) (p q : mon n), degc n p = degc n q -> orderc n p q -> total_orderc n p q.
Hint Resolve total_orderc0 total_orderc1 : core.
End lexi_order.

Theorem orderc_dec : forall (n : nat) (a b : mon n), {orderc n a b} + {orderc n b a} + {a = b}.
intros n a; elim a; auto.
intro b.
rewrite <- (mon_0 b); auto.
intros d n0 m H' b; try assumption.
rewrite <- (proj_ok d b).
case (H' (pmon2 (S d) b)).
intro H'0; case H'0.
intro H'1.
left; left; auto.
intro H'1; left; right; auto.
intro H'0.
elim (lt_eq_lt_dec n0 (pmon1 (S d) b)); [ intro H'1; elim H'1 | idtac ]; intro H'2; auto.
left; right; auto.
rewrite H'0; auto.
right; rewrite H'0; rewrite H'2; auto.
left; left; rewrite H'0; auto.
