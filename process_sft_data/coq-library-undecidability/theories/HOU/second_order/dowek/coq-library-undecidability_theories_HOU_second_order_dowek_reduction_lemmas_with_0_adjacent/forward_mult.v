Set Implicit Arguments.
Require Import List Arith Lia.
From Undecidability.HOU Require Import std.std calculus.calculus.
Import ListNotations.
From Undecidability.HOU.second_order Require Import diophantine_equations dowek.encoding.
Require Import Undecidability.HOU.unification.nth_order_unification.
Set Default Proof Using "Type".
Section EquationEquivalences.
Variable (X: Const) (sigma: fin -> exp X).
Hypothesis (N: forall x, normal (sigma x)).
Section Variables.
End Variables.
Section Constants.
Variable (x n c: nat).
Hypothesis (EQx: sigma x = enc n).
End Constants.
Section Addition.
Variable (x y z n m p c: nat).
Hypothesis (EQx: sigma x = enc m) (EQy: sigma y = enc n) (EQz: sigma z = enc p).
End Addition.
Section Multiplication.
Variable (x y z n m p c: nat).
Hypothesis (EQx: sigma x = enc m) (EQy: sigma y = enc n) (EQz: sigma z = enc p).
End Multiplication.
End EquationEquivalences.
Section Forward.
Variable (X: Const) (E: list deq).
Implicit Types (x y z: nat) (c: nat).
Definition encs theta: fin -> exp X := theta >> enc.
End Forward.
Section Backward.
Variable (X: Const).
Implicit Types (sigma: nat -> exp X) (x y z c n: nat).
Definition sub_sol sigma x := match dec_enc (sigma x) with | inl (exist _ k _) => k | inr _ => 0 end.
End Backward.

Lemma forward_mult : m * n = p -> sigma • fst (mulEQ x y z) ≡ sigma • snd (mulEQ x y z).
Proof using EQz EQy EQx.
intros; unfold mulEQ, fst, snd; asimpl.
now rewrite EQx, EQy, EQz, <-enc_mul, H.
