Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.Synthetic.Definitions.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition bin (x: list nat) : list bool := flat_map (fun (a : nat) => true :: (repeat false a) ++ [true]) x.
Definition bin_map A := map (fun '(x, y) => (bin x, bin y)) A.

Lemma incl_consE {X: Type} {a: X} {A: list X} {P: list X} : incl (a :: A) P -> In a P /\ incl A P.
Proof.
move=> H.
constructor; move=> *; apply: H; by [left | right].
