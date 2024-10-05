From Undecidability Require Import MaxList.
From Undecidability Require Import TM.Util.TM_facts TM.Code.CodeTM.
From Undecidability Require Import TM.Util.VectorPrelim.
From Undecidability Require Import L.Prelim.MoreList.

Lemma max_list_sumn l : max_list l <= sumn l.
Proof.
unfold max_list.
induction l;cbn.
2:rewrite max_list_rec_max'.
all:nia.
