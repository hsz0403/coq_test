Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.Synthetic.Definitions.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition bin (x: list nat) : list bool := flat_map (fun (a : nat) => true :: (repeat false a) ++ [true]) x.
Definition bin_map A := map (fun '(x, y) => (bin x, bin y)) A.

Lemma bin_appP {x y} : bin (x ++ y) = bin x ++ bin y.
Proof.
by rewrite /bin ? flat_map_concat_map map_app concat_app.
