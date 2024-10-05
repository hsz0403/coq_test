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

Lemma keylem : forall bs : list B, GRBar B R bs -> forall us : list (A * B), bs = sndL us -> MinD us -> GBarlR us.
intros bs H'; elim H'; auto.
intros l H'0 us H'1 H'2.
apply lem1; auto.
rewrite <- H'1; auto.
intros l H'0 H'1 us H'2 H'3; red in |- *.
apply OpenInd with (lt := prod_lt); auto.
exact WFlem1.
intros a H'4.
apply H'1 with (a := snd a); auto.
rewrite H'2; auto.
