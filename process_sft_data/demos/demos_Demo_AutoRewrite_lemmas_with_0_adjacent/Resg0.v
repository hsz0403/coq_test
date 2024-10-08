Require Import Arith.
Require Import Omega.
Section Ackermann.
Variable Ack : nat -> nat -> nat.
Axiom Ack0 : forall m : nat, Ack 0 m = S m.
Axiom Ack1 : forall n : nat, Ack (S n) 0 = Ack n 1.
Axiom Ack2 : forall n m : nat, Ack (S n) (S m) = Ack n (Ack (S n) m).
Hint Rewrite Ack0 Ack1 Ack2 : base0.
End Ackermann.
Section McCarthy.
Variable g : nat -> nat -> nat.
Axiom g0 : forall m : nat, g 0 m = m.
Axiom g1 : forall n m : nat, n > 0 -> m > 100 -> g n m = g (pred n) (m - 10).
Axiom g2 : forall n m : nat, n > 0 -> m <= 100 -> g n m = g (S n) (m + 11).
Hint Rewrite g0 g1 g2 using omega : base1.
End McCarthy.

Lemma Resg0 : g 1 110 = 100.
Proof.
autorewrite with base1 using reflexivity || simpl in |- *.
