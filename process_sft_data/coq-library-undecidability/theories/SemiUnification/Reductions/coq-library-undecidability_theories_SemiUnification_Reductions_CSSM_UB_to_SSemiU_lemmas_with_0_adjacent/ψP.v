Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Relations.Relation_Operators Relations.Operators_Properties.
From Undecidability.StackMachines Require Import SSM.
From Undecidability.StackMachines.Util Require Import CSSM_facts.
Require Import Undecidability.SemiUnification.SemiU.
From Undecidability.SemiUnification.Util Require Import Facts Enumerable.
Require Import ssreflect ssrfun ssrbool.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Module Argument.
Definition embed : config -> nat := to_nat.
Definition unembed : nat -> config := of_nat.
Definition embedP {X: config} : (unembed (embed X) = X) := enumP.
Definition SM_to_SUcs (M: ssm) : list constraint := map (fun '(x, y, a, b, d) => if d then ((a, embed ([], [], x)), (embed ([], [], y), b)) (* ax -> yb *) else ((b, embed ([], [], y)), (embed ([], [], x), a)) (* xa -> by *) ) M.
Section SM.
Context {M : ssm}.
Variable confluent_M : confluent M.
Notation equiv := (@equiv M).
Notation equiv_dec := (@equiv_dec M).
Notation narrow_dec := (@narrow_dec M).
Notation bounded' := (@bounded' M).
Fixpoint nf_aux (i: nat) (X: config) : config := match i with | 0 => X | S i => if equiv_dec (unembed i) X then nf_aux i (unembed i) else nf_aux i X end.
Definition nf (X: config) : config := nf_aux (embed X) X.
Fixpoint ζ (n: nat) (X: config) : term := match n with | 0 => atom (embed (nf X)) | S n => match X with | (A, B, x) => if narrow_dec (A, B, x) then arr (ζ n (A, B++[false], x)) (ζ n (A, B++[true], x)) else atom (embed (nf X)) end end.
Definition ψ (a: bool) (n: nat) (i: nat): term := match unembed i with | (A, B, x) => ζ (n - length B) (A++[a], B, x) end.
End SM.
Fixpoint term_depth_bound (t: term) : nat := match t with | atom _ => 1 | arr s t => 1 + (term_depth_bound s) + (term_depth_bound t) end.
Fixpoint depth_bound (φ: valuation) (xs: list state) : nat := match xs with | [] => 1 | x :: xs => 1 + term_depth_bound (φ x) + depth_bound φ xs end.
Fixpoint descend (t: term) (B: stack) {struct B} : option term := match B with | [] => Some t | b :: B => match t with | atom _ => None | arr s t => descend (if b then t else s) B end end.
Fixpoint ascend (ψ0 ψ1: valuation) (t: term) (A: stack) : term := match A with | [] => t | a :: A => ascend ψ0 ψ1 (substitute (if a then ψ1 else ψ0) t) A end.
Definition interpret (φ ψ0 ψ1: valuation) (X: config) : option term := match X with | (A, B, x) => descend (ascend ψ0 ψ1 (φ (embed ([], [], x))) A) B end.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma ψP {a: bool} {n: nat} {X: config} : ψ a n (embed X) = match X with | (A, B, x) => ζ (n - length B) (A++[a], B, x) end.
Proof.
by rewrite /ψ embedP.
