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

Definition degc : forall n : nat, mon n -> nat.
intros n H'; elim H'.
exact 0.
intros d n1 M n2; exact (n1 + n2).
