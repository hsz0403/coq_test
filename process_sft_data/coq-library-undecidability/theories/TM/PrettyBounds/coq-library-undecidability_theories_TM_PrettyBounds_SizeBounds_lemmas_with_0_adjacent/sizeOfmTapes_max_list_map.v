From Undecidability Require Import MaxList.
From Undecidability Require Import TM.Util.TM_facts TM.Code.CodeTM.
From Undecidability Require Import TM.Util.VectorPrelim.
From Undecidability Require Import L.Prelim.MoreList.

Lemma sizeOfmTapes_max_list_map (sig : Type) (n : nat) (T : tapes sig n) : sizeOfmTapes T = max_list_map (@sizeOfTape _) (vector_to_list T).
Proof.
unfold sizeOfmTapes.
rewrite fold_left_vector_to_list.
rewrite <- vector_to_list_map.
unfold max_list_map, max_list.
apply max_list_rec_eq_foldl.
