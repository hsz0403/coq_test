From Undecidability Require Import MaxList.
From Undecidability Require Import TM.Util.TM_facts TM.Code.CodeTM.
From Undecidability Require Import TM.Util.VectorPrelim.
From Undecidability Require Import L.Prelim.MoreList.

Lemma destruct_vector1 (X : Type) (v : Vector.t X 1) : exists x, v = [| x |].
Proof.
destruct_vector.
eauto.
