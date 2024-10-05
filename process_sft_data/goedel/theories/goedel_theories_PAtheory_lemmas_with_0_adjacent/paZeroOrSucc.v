Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import subAll.
Require Import folReplace.
Require Import folProp.
Require Import folLogic3.
Require Import NN.
Require Import LNN2LNT.
Require Export PA.

Lemma paZeroOrSucc : forall t : Term, SysPrf PA (orH (equal t Zero) (existH (newVar (0 :: freeVarTerm LNT t)) (equal t (Succ (var (newVar (0 :: freeVarTerm LNT t))))))).
Proof.
intros.
set (nv := newVar (0 :: freeVarTerm LNT t)) in *.
apply impE with (substituteFormula LNT (orH (equal (var 0) Zero) (existH nv (equal (var 0) (Succ (var nv))))) 0 t).
rewrite (subFormulaOr LNT).
rewrite (subFormulaEqual LNT).
simpl in |- *.
apply iffE1.
apply (reduceOr LNT).
apply iffRefl.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec nv 0).
elim (newVar1 (0 :: freeVarTerm LNT t)).
fold nv in |- *.
rewrite a.
simpl in |- *.
auto.
induction (In_dec eq_nat_dec nv (freeVarTerm LNT t)).
elim (newVar1 (0 :: freeVarTerm LNT t)).
fold nv in |- *.
simpl in |- *.
auto.
rewrite (subFormulaEqual LNT).
Opaque eq_nat_dec.
simpl in |- *.
Transparent eq_nat_dec.
destruct (eq_nat_dec 0 nv).
elim b.
auto.
apply iffRefl.
apply forallE.
apply induct.
rewrite (subFormulaOr LNT).
apply orI1.
rewrite (subFormulaEqual LNT).
simpl in |- *.
apply eqRefl.
apply forallI.
apply closedPA.
apply impI.
rewrite (subFormulaOr LNT).
apply orI2.
rewrite (subFormulaExist LNT).
induction (eq_nat_dec nv 0).
elim (newVar1 (0 :: freeVarTerm LNT t)).
fold nv in |- *.
simpl in |- *.
auto.
induction (In_dec eq_nat_dec nv (freeVarTerm LNT (Succ (var 0)))).
elim (newVar1 (0 :: freeVarTerm LNT t)).
fold nv in |- *.
simpl in a.
induction a as [H| H].
simpl in |- *.
auto.
elim H.
rewrite (subFormulaEqual LNT).
Opaque eq_nat_dec.
simpl in |- *.
Transparent eq_nat_dec.
induction (nat_rec (fun n : nat => {0 = n} + {0 <> n}) (left (0 <> 0) (refl_equal 0)) (fun (m : nat) (_ : {0 = m} + {0 <> m}) => right (0 = S m) (O_S m)) nv).
elim b.
auto.
fold var in |- *.
fold (Succ (var nv)) in |- *.
apply sysWeaken.
apply existI with (var 0).
rewrite (subFormulaEqual LNT).
simpl in |- *.
destruct (eq_nat_dec nv 0).
elim b1; auto.
change match nv as n return ({0 = n} + {0 <> n}) with | 0 => left (0 <> 0) (refl_equal 0) | S m => right (0 = S m) (O_S m) end with (eq_nat_dec 0 nv).
destruct (eq_nat_dec 0 nv).
elim b1.
auto.
simpl.
destruct (eq_nat_dec nv nv).
apply eqRefl.
elim n1.
reflexivity.
