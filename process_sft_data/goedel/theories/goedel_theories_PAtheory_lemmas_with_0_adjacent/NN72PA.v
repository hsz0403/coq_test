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

Lemma NN72PA : SysPrf PA (LNN2LNT_formula NN7).
Proof.
simpl in |- *.
apply forallI.
apply closedPA.
rewrite translateLT1.
simpl in |- *.
set (nv := newVar (0 :: 2 :: 1 :: 0 :: nil)) in *.
fold var in |- *.
fold Zero in |- *.
fold (Succ (var nv)) in |- *.
fold (Plus (var 0) (Succ (var nv))) in |- *.
apply nnI.
apply forallI.
apply closedPA.
apply impE with (notH (equal (Succ (Plus (var 0) (var nv))) Zero)).
apply cp2.
apply impI.
apply eqTrans with (Plus (var 0) (Succ (var nv))).
apply sysWeaken.
apply eqSym.
apply pa4.
apply Axm; right; constructor.
apply pa1.
