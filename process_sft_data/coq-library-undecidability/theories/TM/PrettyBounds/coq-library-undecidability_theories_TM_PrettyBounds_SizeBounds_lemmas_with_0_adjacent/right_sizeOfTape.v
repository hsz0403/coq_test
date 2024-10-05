From Undecidability Require Import MaxList.
From Undecidability Require Import TM.Util.TM_facts TM.Code.CodeTM.
From Undecidability Require Import TM.Util.VectorPrelim.
From Undecidability Require Import L.Prelim.MoreList.

Lemma right_sizeOfTape sig' (t:tape sig') : length (right t) <= sizeOfTape t.
Proof.
destruct t;cbn.
all:autorewrite with list;cbn.
all:nia.
