Require Import List.
Require Import Bar.
Require Import OpenIndGoodRel.
Require Import Lt.
Require Import Wf_nat.
Require Import Inverse_Image.
Require Import Monomials.
Definition DecRel (A : Set) (R : Rel A) := forall x y : A, {R x y} + {~ R x y}.
Definition NegRel (A : Set) (R : Rel A) (x y : A) := ~ R x y.
Definition ProdRel (A B : Set) (R : Rel A) (S : Rel B) (x y : A * B) := R (fst x) (fst y) /\ S (snd x) (snd y).
Section Dickson.
Variable A B : Set.
Variable lt : Rel A.
Variable R : Rel B.
Variable wfgt : well_founded lt.
Variable declt : DecRel A lt.
Variable wR : WR B R.
Definition leq (a b : A) := ~ lt b a.
Definition GBarlR := GRBar (A * B) (ProdRel A B leq R).
Definition sndL := map (fun p : A * B => snd p).
Definition MinD := Min (A * B) (fun p q : A * B => lt (fst p) (fst q)) (ProdRel A B leq R).
Definition prod_lt (a b : A * B) := lt (fst a) (fst b).
End Dickson.
Definition jj : forall d : nat, mon d := (fix jj (d : nat) : mon d := match d as n return (mon n) with | O => n_0 | S n => c_n n 0 (jj n) end).
Definition monLift (n : nat) (p : nat * mon n) := match p with | (x, m) => c_n n x m end.

Theorem nat_double_ind_set : forall R : nat -> nat -> Set, (forall n : nat, R 0 n) -> (forall n : nat, R (S n) 0) -> (forall n m : nat, R n m -> R (S n) (S m)) -> forall n m : nat, R n m.
Proof.
simple induction n; simple induction m; auto.
