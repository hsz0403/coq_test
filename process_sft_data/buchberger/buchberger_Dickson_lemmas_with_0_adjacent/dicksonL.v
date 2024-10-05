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

Lemma dicksonL : forall n : nat, WR (mon n) (mdiv n).
intro.
unfold WR in |- *.
elim n.
apply zRV_WR.
intros.
cut (WR (nat * mon n0) (ProdRel nat (mon n0) (leq nat lt) (mdiv n0))); [ intros | exact (keylem_cor nat (mon n0) lt (mdiv n0) lt_wf dec_lt H) ].
unfold WR in H0.
change (GRBar (mon (S n0)) (mdiv (S n0)) (map (monLift n0) nil)) in |- *.
apply subRelGRBar with (R := ProdRel nat (mon n0) (leq nat lt) (mdiv n0)); auto.
intros a b; case a; case b; simpl in |- *; auto.
intros n1 m n2 m0 H'; inversion H'; auto.
apply mdiv_cons; auto.
apply leq2le; auto.
intros b; exists (pmon1 (S n0) b, pmon2 (S n0) b); simpl in |- *.
apply sym_eq; apply proj_ok; auto.
