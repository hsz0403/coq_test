Set Implicit Arguments.
Require Import RelationClasses Morphisms Wf List Lia Init.Nat Setoid.
From Undecidability.HOU Require Import calculus.calculus unification.unification.
From Undecidability.HOU.second_order Require Export diophantine_equations goldfarb.encoding goldfarb.multiplication.
Import ListNotations.
Set Default Proof Using "Type".
Section EquationEquivalences.
Variable (sigma: fin -> exp ag).
Hypothesis (N: forall x, normal (sigma x)).
Section Variables.
End Variables.
Section Constants.
Variable (n: nat) (x: nat).
Hypothesis (Ex: encodes (sigma (F x)) n).
End Constants.
Section Addition.
Variable (m n p: nat) (x y z: nat).
Hypothesis (Ex: encodes (sigma (F x)) m) (Ey: encodes (sigma (F y)) n) (Ez: encodes (sigma (F z)) p).
End Addition.
Section Multiplication.
Variable (m n p: nat) (x y z: nat).
Hypothesis (Ex: encodes (sigma (F x)) m) (Ey: encodes (sigma (F y)) n) (Ez: encodes (sigma (F z)) p).
End Multiplication.
End EquationEquivalences.
Section Forward.
Variables (E: list deq).
Definition gf n := lambda enc n (var 0).
Definition enc_sol (sigma: nat -> nat) (x: fin) := match partition_F_G x with | inl (exist _ x _) => gf (sigma x) | inr (exist _ (x,y,z) _) => T (sigma y) (sigma x) end.
End Forward.
Section Backward.
Definition decode_subst (sigma: fin -> exp ag) (N: forall x, normal (sigma x)) (x: fin) := match dec_enc (N (F x)) with | inl (exist _ n _) => n | inr _ => 0 end.
End Backward.
Definition nileq: eq ag := (lambda lambda a, lambda lambda a).
Definition conseqs e1 e2 := match e1, e2 with | (lambda lambda s1, lambda lambda t1), (lambda lambda s2, lambda lambda t2) => (lambda lambda g s1 s2, lambda lambda g t1 t2) | _, _ => nileq end.
Notation foldeqs := (fold_right conseqs nileq).

Lemma foldeqs_typing Gamma E: Gamma ⊢₊₊(2) E : repeat (alpha → alpha → alpha) (length E) -> Gamma ⊢₂(2) (foldeqs E) : alpha → alpha → alpha.
Proof.
remember (repeat (alpha → alpha → alpha) (| E |)) as L.
induction 1 in HeqL |- *; cbn.
-
repeat econstructor.
-
do 2 (destruct s; try solve [repeat econstructor]).
do 2 (destruct t; try solve [repeat econstructor]).
specialize (foldeqs_lambda_lambda E) as (u&v&H'); rewrite H' in *.
cbn in HeqL.
injection HeqL as -> ->.
mp IHeqs_ordertyping; (eauto 2).
inv H0.
inv H4.
inv H.
inv H4.
destruct IHeqs_ordertyping as [T1 T2].
inv T1.
inv H4.
inv T2.
inv H4.
repeat econstructor; (eauto 2).
