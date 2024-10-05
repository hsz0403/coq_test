From Undecidability Require Import MaxList.
From Undecidability Require Import TM.Util.TM_facts TM.Code.CodeTM.
From Undecidability Require Import TM.Util.VectorPrelim.
From Undecidability Require Import L.Prelim.MoreList.

Lemma length_tape_local_right sig' (t:tape sig') : length (tape_local (tape_move_right t)) <= sizeOfTape t.
Proof.
destruct t;cbn.
1-3:nia.
rewrite tape_local_move_right'.
autorewrite with list;cbn.
all:nia.
