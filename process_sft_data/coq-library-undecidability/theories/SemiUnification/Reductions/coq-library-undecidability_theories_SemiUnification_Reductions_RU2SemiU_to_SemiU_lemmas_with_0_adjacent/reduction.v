Require Import List.
Import ListNotations.
Require Import Undecidability.SemiUnification.SemiU.
From Undecidability.SemiUnification.Util Require Import Facts.
Require Import ssreflect ssrfun ssrbool.
Require Import Undecidability.Synthetic.Definitions.

Theorem reduction : RU2SemiU ⪯ SemiU.
Proof.
exists (fun '(s0, s1, t) => [(s0, t); (s1, t)]).
move=> [[s0 s1] t].
constructor.
-
move=> [φ] [ψ0] [ψ1] [Hψ0 Hψ1].
exists φ.
rewrite -Forall_forall ?Forall_norm.
constructor; [by exists ψ0 | by exists ψ1].
-
move=> [φ].
rewrite -Forall_forall ?Forall_norm.
move=> [[ψ0 Hψ0] [ψ1 Hψ1]].
by exists φ, ψ0, ψ1.
