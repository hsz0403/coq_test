Require Import Arith.
Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import folProp.
Require Import subAll.
Require Import folLogic3.
Require Export Languages.
Require Export LNN.
Section NN.
Definition NN1 := forallH 0 (notH (equal (Succ (var 0)) Zero)).
Definition NN2 := forallH 1 (forallH 0 (impH (equal (Succ (var 0)) (Succ (var 1))) (equal (var 0) (var 1)))).
Definition NN3 := forallH 0 (equal (Plus (var 0) Zero) (var 0)).
Definition NN4 := forallH 1 (forallH 0 (equal (Plus (var 0) (Succ (var 1))) (Succ (Plus (var 0) (var 1))))).
Definition NN5 := forallH 0 (equal (Times (var 0) Zero) Zero).
Definition NN6 := forallH 1 (forallH 0 (equal (Times (var 0) (Succ (var 1))) (Plus (Times (var 0) (var 1)) (var 0)))).
Definition NN7 := forallH 0 (notH (LT (var 0) Zero)).
Definition NN8 := forallH 1 (forallH 0 (impH (LT (var 0) (Succ (var 1))) (orH (LT (var 0) (var 1)) (equal (var 0) (var 1))))).
Definition NN9 := forallH 1 (forallH 0 (orH (LT (var 0) (var 1)) (orH (equal (var 0) (var 1)) (LT (var 1) (var 0))))).
Definition NNStar := forallH 1 (forallH 0 (impH (orH (LT (var 0) (var 1)) (equal (var 0) (var 1))) (LT (var 0) (Succ (var 1))))).
Definition NN := Ensembles.Add _ (Ensembles.Add _ (Ensembles.Add _ (Ensembles.Add _ (Ensembles.Add _ (Ensembles.Add _ (Ensembles.Add _ (Ensembles.Add _ (Singleton _ NN1) NN2) NN3) NN4) NN5) NN6) NN7) NN8) NN9.
End NN.

Lemma nn7 : forall a : Term, SysPrf NN (notH (LT a Zero)).
Proof.
intros.
replace (notH (LT a Zero)) with (substituteFormula LNN (notH (LT (var 0) Zero)) 0 a).
apply forallE.
apply Axm; repeat (try right; constructor) || left.
reflexivity.
