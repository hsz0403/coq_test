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

Let Hsa : s <> a.
Proof.
Admitted.

Let Hsl : s <> l.
Proof.
Admitted.

Let Hah : a <> h.
Proof.
Admitted.

Let Hal : a <> l.
Proof.
Admitted.

Let Hhl : h <> l.
Proof.
Admitted.

Fact simulator_length : length simulator = 27+lML.
Proof.
Admitted.

Fact pcp_bsm_size : length simulator = 86+3*length lt+size_cards lt.
Proof.
rewrite simulator_length; unfold lML.
Admitted.

Let HS1 : (1,main_init s a h l 1) <sc (1, simulator).
Proof.
Admitted.

Let HS2 : (14,main_loop s a h l lt 14 (14+lML)) <sc (1, simulator).
Proof.
Admitted.

Let HS3 : (14+lML,main_init s a h l (14+lML)) <sc (1, simulator).
Proof.
Admitted.

Theorem pcp_bsm_sound v : tiles_solvable lt -> (1,simulator) // (1,v) ->> (0,v[nil/s][nil/a][nil/h][nil/l]).
Proof.
intros H1; unfold simulator.
apply subcode_sss_compute_trans with (2 := main_init_spec Hsa Hsh Hsl Hah Hal 1 v); auto.
destruct (main_loop_sound Hsa Hsh Hsl Hah Hal Hhl) with (lt := lt) (i := 14) (p := 14+lML) (v := v[(Zero::nil)/s][nil/a][nil/h][nil/l]) as (w & Hw1 & Hw2); rew vec.
apply subcode_sss_compute_trans with (2 := Hw1); auto.
apply subcode_sss_compute_trans with (2 := main_init_spec Hsa Hsh Hsl Hah Hal (14+lML) _); auto.
bsm sss POP 0 with s 0 0 nil; rew vec.
bsm sss stop; f_equal.
apply vec_pos_ext; intros x.
dest x a; dest x l; dest x h; dest x s.
Admitted.

Let Hsh : s <> h.
Proof.
discriminate.
