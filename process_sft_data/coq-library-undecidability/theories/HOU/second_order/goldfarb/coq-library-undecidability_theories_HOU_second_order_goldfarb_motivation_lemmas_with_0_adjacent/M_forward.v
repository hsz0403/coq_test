Set Implicit Arguments.
Require Import List Lia.
From Undecidability.HOU Require Import std.std axioms.
Import ListNotations.
Set Default Proof Using "Type".
Section Motivation.
Variable (n: nat).
Implicit Type (m p: nat) (M N: list (nat * nat)).
Definition step '(a, b) := (n + a, 1 + b).
Notation Step X := (map step X).
Definition t k := (k * n, k).
Definition T k := tab t k.
Definition Mrel m p M := M ++ [(p, m)] = t 0 :: Step M.
End Motivation.

Lemma M_forward m: Mrel m (m * n) (T m).
Proof.
unfold Mrel, T; change (_ ++ _) with (tab t (S m)).
now rewrite tab_S, tab_map.
