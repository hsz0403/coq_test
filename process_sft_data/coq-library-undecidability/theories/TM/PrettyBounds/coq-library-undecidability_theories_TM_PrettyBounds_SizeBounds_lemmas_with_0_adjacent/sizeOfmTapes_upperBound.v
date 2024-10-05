From Undecidability Require Import MaxList.
From Undecidability Require Import TM.Util.TM_facts TM.Code.CodeTM.
From Undecidability Require Import TM.Util.VectorPrelim.
From Undecidability Require Import L.Prelim.MoreList.

Lemma sizeOfmTapes_upperBound (sig : Type) (n : nat) (tps : tapes sig n) : forall t, Vector.In t tps -> sizeOfTape t <= sizeOfmTapes tps.
Proof.
intros.
rewrite sizeOfmTapes_max_list_map.
apply max_list_map_ge.
now apply vector_to_list_In.
