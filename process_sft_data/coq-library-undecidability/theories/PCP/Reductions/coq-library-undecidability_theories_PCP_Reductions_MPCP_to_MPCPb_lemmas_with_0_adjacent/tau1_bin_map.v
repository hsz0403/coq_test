Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.Synthetic.Definitions.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition bin (x: list nat) : list bool := flat_map (fun (a : nat) => true :: (repeat false a) ++ [true]) x.
Definition bin_map A := map (fun '(x, y) => (bin x, bin y)) A.

Lemma tau1_bin_map {A : list (list nat * list nat)} : tau1 (bin_map A) = bin (tau1 A).
Proof.
elim: A; first done.
move=> [x y] A IH /=.
by rewrite bin_appP IH.
