From Coq Require Import FunInd.
From Undecidability Require Import TM.Code.Copy.
From Undecidability Require Import TM.Code.CodeTM.
From Undecidability Require Import TM.Compound.Compare.
From Undecidability Require Import TM.Basic.Basic.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Compound.TMTac TM.Compound.Multi.
From Undecidability Require Import TM.Lifting.LiftTapes.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Set Default Proof Using "Type".
Section CompareValues.
Variable sigX : finType.
Variable (X : eqType) (cX : codable sigX X).
Hypothesis cX_injective : forall x1 x2, cX x1 = cX x2 -> x1 = x2.
Definition CompareValues_Rel : pRel sigX^+ bool 2 := fun tin '(yout, tout) => forall (x1 x2 : X) (sx sy : nat), tin[@Fin0] ≃(;sx) x1 -> tin[@Fin1] ≃(;sy) x2 -> (yout = if Dec (x1=x2) then true else false) /\ tout[@Fin0] ≃(;sx) x1 /\ tout[@Fin1] ≃(;sy) x2.
Definition CompareValues : pTM sigX^+ bool 2 := Switch (Compare (@isStop sigX)) (fun res => Return (LiftTapes (MoveToSymbol_L (@isStart sigX) id) [|Fin0|];; LiftTapes (MoveToSymbol_L (@isStart sigX) id) [|Fin1|]) res).
Definition CompareValues_steps {sigX X : Type} {cX : codable sigX X} (x1 x2 : X) := 29 + 6 * max (size x1) (size x2) + 4 * (size x1) + 4 * (size x2).
Definition CompareValues_T : tRel sigX^+ 2 := fun tin k => exists (x1 x2 : X), tin[@Fin0] ≃ x1 /\ tin[@Fin1] ≃ x2 /\ CompareValues_steps x1 x2 <= k.
End CompareValues.
Arguments CompareValues_steps {sigX X cX} : simpl never.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister HoareTactics.
Section CompareValues.
Variable (sigX : finType) (X : eqType) (cX : codable sigX X).
Hypothesis (HInj : forall x y, cX x = cX y -> x = y).
End CompareValues.

Lemma list_length_neq (X : Type) (xs ys : list X) : length xs <> length ys -> xs <> ys.
Proof.
now intros ? ->.
