Require Import List Arith Lia Bool.
From Undecidability.Shared.Libs.DLW Require Import utils list_bool pos vec subcode sss.
From Undecidability.StackMachines.BSM Require Import tiles_solvable bsm_defs bsm_utils.
Set Implicit Arguments.
Set Default Proof Using "Type".
Tactic Notation "rew" "length" := autorewrite with length_db.
Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).
Local Notation "P // s -[ k ]-> t" := (sss_steps (@bsm_sss _) P k s t).
Local Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).
Local Notation "P // s ~~> t" := (sss_output (@bsm_sss _) P s t).
Section Simulator.
Hint Rewrite main_loop_length main_init_length : length_db.
Variable (lt : list ((list bool) *(list bool))).
Let n := 4.
Let s : pos 4 := pos0.
Let h : pos 4 := pos1.
Let l : pos 4 := pos2.
Let a : pos 4 := pos3.
Let Hsa : s <> a.
Proof.
discriminate.
Let Hsh : s <> h.
Proof.
discriminate.
Let Hsl : s <> l.
Proof.
discriminate.
Let Hah : a <> h.
Proof.
discriminate.
Let Hal : a <> l.
Proof.
discriminate.
Let Hhl : h <> l.
Proof.
discriminate.
Let lML := length_main_loop lt.
Definition pcp_bsm := (* 1 *) main_init s a h l 1 ++ (* 14 *) main_loop s a h l lt 14 (14+lML) ++ (* 14+lML *) main_init s a h l (14+lML) ++ (* 27+lML *) POP s 0 0 :: nil.
Notation simulator := pcp_bsm.
Fact simulator_length : length simulator = 27+lML.
Proof.
unfold simulator; rew length; unfold lML; lia.
Fact pcp_bsm_size : length simulator = 86+3*length lt+size_cards lt.
Proof.
rewrite simulator_length; unfold lML.
rewrite main_loop_size; lia.
Let HS1 : (1,main_init s a h l 1) <sc (1, simulator).
Proof.
unfold simulator; auto.
Let HS2 : (14,main_loop s a h l lt 14 (14+lML)) <sc (1, simulator).
Proof.
unfold simulator; auto.
Let HS3 : (14+lML,main_init s a h l (14+lML)) <sc (1, simulator).
Proof.
unfold simulator; auto.
Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.
End Simulator.

Let Hah : a <> h.
Proof.
discriminate.
