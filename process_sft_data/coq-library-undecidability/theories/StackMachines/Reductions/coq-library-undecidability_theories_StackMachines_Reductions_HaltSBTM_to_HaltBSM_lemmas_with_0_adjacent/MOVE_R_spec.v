Require Import Undecidability.TM.SBTM.
Require Import Undecidability.Shared.Libs.PSL.Vectors.FinNotation Undecidability.Shared.Libs.PSL.Vectors.Vectors Undecidability.Shared.Libs.PSL.EqDec.
Require Import List Arith Lia Bool.
From Undecidability.Shared.Libs.DLW Require Import utils list_bool pos vec subcode sss.
From Undecidability.StackMachines.BSM Require Import bsm_defs.
Import ListNotations.
Import VectorNotations2.
Local Open Scope vector.
Set Default Proof Using "Type".
Tactic Notation "rew" "length" := autorewrite with length_db.
Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).
Local Notation "P // s -[ k ]-> t" := (sss_steps (@bsm_sss _) P k s t).
Local Notation "P // r -+> s" := (sss_progress(@bsm_sss _) P r s).
Local Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).
Definition enc_tape (t : tape) : Vector.t (list bool) 4 := [| left t ; match curr t with Some c => [c] | None => [] end ; right t ; [] |]%vector.
Ltac solve_sc := repeat match goal with | [ |- (?i, _) <sc (?i, _)] => eexists [], _; split; [reflexivity | cbn; try lia] | [ |- (?o + ?i, ?c1) <sc (?i, ?c2) ] => exists (firstn o c2); eexists; split; [ reflexivity | cbn; lia] | [ |- (?l, ?c1) <sc (?i, ?c2) ] => let x := fresh "x" in let H := fresh "H" in evar (x : nat); assert (l = x + i); [ ring_simplify; subst x; reflexivity | rewrite H; subst x ] end.
Hint Extern 0 => solve_sc : core.
Notation CURR := (Fin1 : Fin.t 4).
Notation LEFT := (Fin0 : Fin.t 4).
Notation RIGHT := (Fin2 : Fin.t 4).
Notation ZERO := (Fin3 : Fin.t 4).
Notation CURR_ := 1.
Notation LEFT_ := 0.
Notation RIGHT_ := 2.
Notation ZERO_ := 3.
Notation JMP i := (POP ZERO i i).
Section fixi.
Variable i : nat.
Notation END := (23 + i).
Definition MOVE_L := [ (* i *) POP CURR (8 + i) (5 + i) ; (* i + 1 *) POP LEFT (14 + i) (12 + i) ; (* i + 2 *) PUSH CURR true ; (* i + 3 *) PUSH RIGHT true; (* i + 4 *) JMP END ; (* i + 5 *) POP LEFT (17 + i) END ; (* i + 6 *) PUSH CURR true ; (* i + 7 *) JMP END ; (* i + 8 *) POP LEFT (21 + i) (19 + i) ; (* i + 9 *) PUSH CURR true ; (* i + 10 *) PUSH RIGHT false ; (* i + 11 *) JMP END ; (* i + 12 *) PUSH RIGHT true ; (* i + 13 *) JMP END ; (* i + 14 *) PUSH CURR false ; (* i + 15 *) PUSH RIGHT true ; (* i + 16 *) JMP END ; (* i + 17 *) PUSH CURR false ; (* i + 18 *) JMP END ; (* i + 19 *) PUSH RIGHT false ; (* i + 20 *) JMP END ; (* i + 21 *) PUSH CURR false ; (* i + 22 *) PUSH RIGHT false ].
Fact MOVE_L_length : length MOVE_L = 23.
Proof.
reflexivity.
Fact MOVE_L_spec t : (i,MOVE_L) // (i, enc_tape t) ->> (END, enc_tape (mv Lmove t)).
Proof.
unfold MOVE_L.
destruct t as [[ [ | l ls] [ [] | ] ] rs].
-
bsm sss POP 1 with CURR (8 + i) (5 + i) [].
bsm sss POP empty with LEFT (14 + i) (12 + i).
bsm sss PUSH with RIGHT true.
bsm sss POP empty with ZERO END END.
bsm sss stop.
-
bsm sss POP 0 with CURR (8 + i) (5 + i) [].
bsm sss POP empty with LEFT (21 + i) (19 + i).
bsm sss PUSH with RIGHT false.
bsm sss POP empty with ZERO END END.
bsm sss stop.
-
bsm sss POP empty with CURR (8 + i) (5 + i).
bsm sss POP empty with LEFT (17 + i) END.
bsm sss stop.
-
bsm sss POP 1 with CURR (8 + i) (5 + i) [].
destruct l.
+
bsm sss POP 1 with LEFT (14 + i) (12 + i) ls.
bsm sss PUSH with CURR true.
bsm sss PUSH with RIGHT true.
bsm sss POP empty with ZERO END END.
bsm sss stop.
+
bsm sss POP 0 with LEFT (14 + i) (12 + i) ls.
bsm sss PUSH with CURR false.
bsm sss PUSH with RIGHT true.
bsm sss POP empty with ZERO END END.
bsm sss stop.
-
bsm sss POP 0 with CURR (8 + i) (5 + i) [].
destruct l.
+
bsm sss POP 1 with LEFT (21 + i) (19 + i) ls.
bsm sss PUSH with CURR true.
bsm sss PUSH with RIGHT false.
bsm sss POP empty with ZERO END END.
bsm sss stop.
+
bsm sss POP 0 with LEFT (21 + i) (19 + i) ls.
bsm sss PUSH with CURR false.
bsm sss PUSH with RIGHT false.
bsm sss stop.
-
bsm sss POP empty with CURR (8 + i) (5 + i).
destruct l.
+
bsm sss POP 1 with LEFT (17 + i) END ls.
bsm sss PUSH with CURR true.
bsm sss POP empty with ZERO END END.
bsm sss stop.
+
bsm sss POP 0 with LEFT (17 + i) END ls.
bsm sss PUSH with CURR false.
bsm sss POP empty with ZERO END END.
bsm sss stop.
Definition MOVE_R := [ (* i *) POP CURR (8 + i) (5 + i) ; (* i + 1 *) POP RIGHT (14 + i) (12 + i) ; (* i + 2 *) PUSH CURR true ; (* i + 3 *) PUSH LEFT true; (* i + 4 *) JMP END ; (* i + 5 *) POP RIGHT (17 + i) END ; (* i + 6 *) PUSH CURR true ; (* i + 7 *) JMP END ; (* i + 8 *) POP RIGHT (21 + i) (19 + i) ; (* i + 9 *) PUSH CURR true ; (* i + 10 *) PUSH LEFT false ; (* i + 11 *) JMP END ; (* i + 12 *) PUSH LEFT true ; (* i + 13 *) JMP END ; (* i + 14 *) PUSH CURR false ; (* i + 15 *) PUSH LEFT true ; (* i + 16 *) JMP END ; (* i + 17 *) PUSH CURR false ; (* i + 18 *) JMP END ; (* i + 19 *) PUSH LEFT false ; (* i + 20 *) JMP END ; (* i + 21 *) PUSH CURR false ; (* i + 22 *) PUSH LEFT false ].
Fact MOVE_R_length : length MOVE_R = 23.
Proof.
reflexivity.
Fact MOVE_R_spec t : (i,MOVE_R) // (i, enc_tape t) ->> (END, enc_tape (mv Rmove t)).
Proof.
unfold MOVE_R.
destruct t as [[ls c] rs]; destruct rs as [ | r rs], c as [ [] | ].
-
bsm sss POP 1 with CURR (8 + i) (5 + i) [].
bsm sss POP empty with RIGHT (14 + i) (12 + i).
bsm sss PUSH with LEFT true.
bsm sss POP empty with ZERO END END.
bsm sss stop.
-
bsm sss POP 0 with CURR (8 + i) (5 + i) [].
bsm sss POP empty with RIGHT (21 + i) (19 + i).
bsm sss PUSH with LEFT false.
bsm sss POP empty with ZERO END END.
bsm sss stop.
-
bsm sss POP empty with CURR (8 + i) (5 + i).
bsm sss POP empty with RIGHT (17 + i) END.
bsm sss stop.
-
bsm sss POP 1 with CURR (8 + i) (5 + i) [].
destruct r.
+
bsm sss POP 1 with RIGHT (14 + i) (12 + i) rs.
bsm sss PUSH with CURR true.
bsm sss PUSH with LEFT true.
bsm sss POP empty with ZERO END END.
bsm sss stop.
+
bsm sss POP 0 with RIGHT (14 + i) (12 + i) rs.
bsm sss PUSH with CURR false.
bsm sss PUSH with LEFT true.
bsm sss POP empty with ZERO END END.
bsm sss stop.
-
bsm sss POP 0 with CURR (8 + i) (5 + i) [].
destruct r.
+
bsm sss POP 1 with RIGHT (21 + i) (19 + i) rs.
bsm sss PUSH with CURR true.
bsm sss PUSH with LEFT false.
bsm sss POP empty with ZERO END END.
bsm sss stop.
+
bsm sss POP 0 with RIGHT (21 + i) (19 + i) rs.
bsm sss PUSH with CURR false.
bsm sss PUSH with LEFT false.
bsm sss stop.
-
bsm sss POP empty with CURR (8 + i) (5 + i).
destruct r.
+
bsm sss POP 1 with RIGHT (17 + i) END rs.
bsm sss PUSH with CURR true.
bsm sss POP empty with ZERO END END.
bsm sss stop.
+
bsm sss POP 0 with RIGHT (17 + i) END rs.
bsm sss PUSH with CURR false.
bsm sss POP empty with ZERO END END.
bsm sss stop.
End fixi.
Section fixM.
Variable M : SBTM.
Notation δ := (trans M).
Notation "! p" := (proj1_sig (Fin.to_nat p)) (at level 1).
Notation c := 76.
Local Notation "'if!' x 'is' p 'then' a 'else' b" := (match x with p => a | _ => b end) (at level 0, p pattern).
Notation END := ((2 + num_states M) * c).
Definition PROG (i : Fin.t (S (num_states M))) := let off := c * !i in [ (* off *) POP CURR (26 + off) (51 + off) ; (* 1 + off *) PUSH CURR (if! δ (i, Some true) is Some (_, Some false, _) then false else true) ] ++ (* 2 + off *) match δ (i, Some true) with Some (_, _, Rmove) => MOVE_R (2 + off) | Some (_, _, Lmove) => MOVE_L (2 + off) | _ => repeat (JMP (25 + off)) 23 end ++ [ (* 25 + off *) JMP (match δ (i, Some true) with None => END | Some (q', _, _) => (c * ! q') end) ; (* 26 + off *) PUSH CURR (if! δ (i, Some false) is Some (_, Some true, _) then true else false) ] ++ (* 27 + off *) match δ (i, Some false) with Some (_, _, Rmove) => MOVE_R (27 + off) | Some (_, _, Lmove) => MOVE_L (27 + off) | _ => repeat (JMP (50 + off)) 23 end ++ [ (* 50 + off *) JMP (match δ (i, Some false) with None => END | Some (q', _, _) => (c * ! q') end) ; (* 51 + off *) match δ (i, None) with None => JMP END | Some (_, Some w, _) => PUSH CURR w | Some _ => JMP (52 + off) end ] ++ (* 52 + off *) match δ (i, None) with Some (_, _, Rmove) => MOVE_R (52 + off) | Some (_, _, Lmove) => MOVE_L (52 + off) | _ => repeat (JMP (75 + off)) 23 end ++ [ (* 75 + off *) JMP (match δ (i, None) with None => END | Some (q', _, _) => (c * ! q') end ) ] .
Fact PROG_length i : length (PROG i) = c.
Proof.
unfold PROG.
rewrite app_length.
destruct (δ (i, Some false)) as [ [[? []] []] | ] eqn:E1; destruct (δ (i, Some true)) as [ [[? []] []] | ] eqn:E2; destruct (δ (i, None)) as [ [[? []] []] | ] eqn:E3.
all:reflexivity.
Fact PROG_spec (i : Fin.t (S (num_states M))) t : (c * !i, PROG i) // (c * !i, enc_tape t) -+> match δ (i, curr t) with None => (END, enc_tape t) | Some (q', w, m) => (c * !q' , enc_tape (mv m (wr w t))) end.
Proof.
set (off := c * !i).
destruct t as [[ls [ [] | ]] rs] eqn:Eq_tape.
-
cbn [curr].
eapply sss_progress_compute_trans.
exists 1.
split.
lia.
econstructor.
2:econstructor.
eapply subcode_sss_step with (P := (off, [POP CURR (26 + off) (51 + off)])).
auto.
eapply in_sss_step with (l := []).
cbn; lia.
econstructor 3.
reflexivity.
unfold PROG.
destruct (δ (i, Some true)) as [ [[q' w] m] | ] eqn:Eq_nxt.
+
edestruct (@case_Some_false w) as [ [H H0] | [H H0]].
*
rewrite H.
bsm sss PUSH with CURR false.
destruct m eqn:Eq_mv.
--
eapply subcode_sss_compute_trans with (P := (2+off, MOVE_L (2 + off))).
eauto.
cbn - [plus mult].
eapply (MOVE_L_spec (2 + off) (ls, Some Zero, rs)).
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
rewrite H0.
reflexivity.
--
eapply subcode_sss_compute_trans with (P := (2+off, MOVE_R (2 + off))).
eauto.
cbn - [plus mult].
eapply (MOVE_R_spec (2 + off) (ls, Some Zero, rs)).
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
rewrite H0.
reflexivity.
--
bsm sss POP empty with ZERO (25 + off) (25 + off).
bsm sss POP empty with ZERO (c * !q') (c * !q').
bsm sss stop.
subst; reflexivity.
*
rewrite H.
bsm sss PUSH with CURR true.
destruct m eqn:Eq_mv.
--
eapply subcode_sss_compute_trans with (P := (2+off, MOVE_L (2 + off))).
eauto.
cbn - [plus mult].
eapply (MOVE_L_spec (2 + off) (ls, Some One, rs)).
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
destruct w as [ [] | ]; try reflexivity.
congruence.
--
eapply subcode_sss_compute_trans with (P := (2+off, MOVE_R (2 + off))).
eauto.
cbn - [plus mult].
eapply (MOVE_R_spec (2 + off) (ls, Some One, rs)).
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
destruct w as [ [] | ]; try reflexivity.
congruence.
--
bsm sss POP empty with ZERO (25 + off) (25 + off).
bsm sss POP empty with ZERO (c * !q') (c * !q').
bsm sss stop.
destruct w as [ [] | ]; try reflexivity.
congruence.
+
bsm sss PUSH with CURR true.
bsm sss POP empty with ZERO (25 + off) (25 + off).
bsm sss POP empty with ZERO END END.
bsm sss stop.
-
cbn [curr].
eapply sss_progress_compute_trans.
exists 1.
split.
lia.
econstructor.
2:econstructor.
eapply subcode_sss_step with (P := (off, [POP CURR (26 + off) (51 + off)])).
auto.
eapply in_sss_step with (l := []).
cbn; lia.
econstructor 2.
reflexivity.
unfold PROG.
eapply subcode_sss_compute_trans; try eapply subcode1.
2:{
bsm sss stop.
}
destruct (δ (i, Some false)) as [ [[q' w] m] | ] eqn:Eq_nxt.
+
edestruct (@case_Some_true w) as [ [] | []].
*
rewrite H.
change (76 * !i) with off.
bsm sss PUSH with CURR true.
destruct m eqn:Eq_mv.
--
eapply subcode_sss_compute_trans with (P := (27+off, MOVE_L (27 + off))).
eauto.
eapply (MOVE_L_spec (27 + off) (ls, Some One, rs)).
replace (23 + (27 + off)) with (24 + (26 + off)) by lia.
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
rewrite H0.
reflexivity.
--
eapply subcode_sss_compute_trans with (P := (27 +off, MOVE_R (27 + off))).
eauto.
eapply (MOVE_R_spec (27 + off) (ls, Some One, rs)).
replace (23 + (27 + off)) with (24 + (26 + off)) by lia.
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
rewrite H0.
reflexivity.
--
bsm sss POP empty with ZERO (50 + off) (50 + off).
replace (50 + off) with (24 + (26 + off)) by lia.
bsm sss POP empty with ZERO (c * !q') (c * !q').
bsm sss stop.
subst; reflexivity.
*
rewrite H.
change (76 * !i) with off.
bsm sss PUSH with CURR false.
destruct m eqn:Eq_mv.
--
eapply subcode_sss_compute_trans with (P := (27+off, MOVE_L (27 + off))).
replace (27 + off) with (1 + (26 + off)) at 1 by lia.
eauto.
eapply (MOVE_L_spec (27 + off) (ls, Some false, rs)).
replace (23 + (27 + off)) with (24 + (26 + off)) by lia.
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
destruct w as [ [] | ]; try reflexivity.
congruence.
--
eapply subcode_sss_compute_trans with (P := (27 +off, MOVE_R (27 + off))).
replace (27 + off) with (1 + (26 + off)) at 1 by lia.
eauto.
eapply (MOVE_R_spec (27 + off) (ls, Some false, rs)).
replace (23 + (27 + off)) with (24 + (26 + off)) by lia.
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
destruct w as [ [] | ]; try reflexivity.
congruence.
--
bsm sss POP empty with ZERO (50 + off) (50 + off).
replace (50 + off) with (24 + (26 + off)) by lia.
bsm sss POP empty with ZERO (c * !q') (c * !q').
bsm sss stop.
destruct w as [ [] | ]; try reflexivity.
congruence.
+
change (76 * !i) with off.
bsm sss PUSH with CURR false.
bsm sss POP empty with ZERO (50 + off) (50 + off).
replace (50 + off) with (24 + (26 + off)) by lia.
bsm sss POP empty with ZERO END END.
bsm sss stop.
-
cbn [curr].
eapply sss_progress_compute_trans.
exists 1.
split.
lia.
econstructor.
2:econstructor.
eapply subcode_sss_step with (P := (off, [POP CURR (26 + off) (51 + off)])).
auto.
eapply in_sss_step with (l := []).
cbn; lia.
econstructor 1.
reflexivity.
unfold PROG.
eapply subcode_sss_compute_trans; try eapply subcode2.
2:{
bsm sss stop.
}
destruct (δ (i, None)) as [ [[q' w] m] | ] eqn:Eq_nxt.
+
edestruct (@case_None w) as [ [] | []].
*
rewrite H.
change (76 * !i) with off.
bsm sss POP empty with ZERO (52 + off) (52 + off).
destruct m eqn:Eq_mv.
--
eapply subcode_sss_compute_trans with (P := (52+off, MOVE_L (52 + off))).
eauto.
eapply (MOVE_L_spec (52 + off) (ls, None, rs)).
replace (23 + (52 + off)) with (24 + (51 + off)) by lia.
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
rewrite H0.
reflexivity.
--
eapply subcode_sss_compute_trans with (P := (52 +off, MOVE_R (52 + off))).
eauto.
eapply (MOVE_R_spec (52 + off) (ls, None, rs)).
replace (23 + (52 + off)) with (24 + (51 + off)) by lia.
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
rewrite H0.
reflexivity.
--
replace (52 + off) with (1 + (51 + off)) by lia.
bsm sss POP empty with ZERO (75 + off) (75 + off).
replace (75 + off) with (24 + (51 + off)) by lia.
bsm sss POP empty with ZERO (c * !q') (c * !q').
bsm sss stop.
subst; reflexivity.
*
destruct w eqn:Eq_w.
--
change (76 * !i) with off.
bsm sss PUSH with CURR b.
destruct m eqn:Eq_mv.
++
eapply subcode_sss_compute_trans with (P := (52+off, MOVE_L (52 + off))).
replace (52 + off) with (1 + (51 + off)) at 1 by lia.
eauto.
eapply (MOVE_L_spec (52 + off) (ls, Some b, rs)).
replace (23 + (52 + off)) with (24 + (51 + off)) by lia.
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
++
eapply subcode_sss_compute_trans with (P := (52 +off, MOVE_R (52 + off))).
replace (52 + off) with (1 + (51 + off)) at 1 by lia.
eauto.
eapply (MOVE_R_spec (52 + off) (ls, Some b, rs)).
replace (23 + (52 + off)) with (24 + (51 + off)) by lia.
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
++
bsm sss POP empty with ZERO (75 + off) (75 + off).
replace (75 + off) with (24 + (51 + off)) by lia.
bsm sss POP empty with ZERO (c * !q') (c * !q').
bsm sss stop.
--
change (76 * !i) with off.
bsm sss POP empty with ZERO (52 + off) (52 + off).
destruct m eqn:Eq_mv.
++
eapply subcode_sss_compute_trans with (P := (52+off, MOVE_L (52 + off))).
replace (52 + off) with (1 + (51 + off)) at 1 by lia.
eauto.
eapply (MOVE_L_spec (52 + off) (ls, None, rs)).
replace (23 + (52 + off)) with (24 + (51 + off) ) by lia.
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
++
eapply subcode_sss_compute_trans with (P := (52 +off, MOVE_R (52 + off))).
replace (52 + off) with (1 + (51 + off)) at 1 by lia.
eauto.
eapply (MOVE_R_spec (52 + off) (ls, None, rs)).
replace (23 + (52 + off)) with (24 + (51 + off)) by lia.
bsm sss POP empty with ZERO (c * ! q') (c * ! q').
bsm sss stop.
++
replace (52 + off) with (1 + (51 + off)) by lia.
bsm sss POP empty with ZERO (75 + off) (75 + off).
replace (75 + off) with (24 + (51 + off)) by lia.
bsm sss POP empty with ZERO (c * !q') (c * !q').
bsm sss stop.
+
change (76 * !i) with off.
bsm sss POP empty with ZERO END END.
bsm sss stop.
Fixpoint sim (n : nat) (H : n <= S (num_states M)) : list (bsm_instr 4).
Proof.
destruct n.
-
exact [].
-
refine (sim n _ ++ _).
abstract lia.
assert (Hn : n < S (num_states M)) by abstract lia.
refine (PROG (Fin.of_nat_lt Hn)).
Defined.
Definition SIM : list (bsm_instr 4).
refine (@sim (S (num_states M)) _).
Proof using M.
abstract lia.
Defined.
Arguments sim _ _ : clear implicits.
Arguments Fin.of_nat_lt _ {_} _.
End fixM.
Require Import Undecidability.Synthetic.Definitions.

Fact MOVE_R_spec t : (i,MOVE_R) // (i, enc_tape t) ->> (END, enc_tape (mv Rmove t)).
Proof.
unfold MOVE_R.
destruct t as [[ls c] rs]; destruct rs as [ | r rs], c as [ [] | ].
-
bsm sss POP 1 with CURR (8 + i) (5 + i) [].
bsm sss POP empty with RIGHT (14 + i) (12 + i).
bsm sss PUSH with LEFT true.
bsm sss POP empty with ZERO END END.
bsm sss stop.
-
bsm sss POP 0 with CURR (8 + i) (5 + i) [].
bsm sss POP empty with RIGHT (21 + i) (19 + i).
bsm sss PUSH with LEFT false.
bsm sss POP empty with ZERO END END.
bsm sss stop.
-
bsm sss POP empty with CURR (8 + i) (5 + i).
bsm sss POP empty with RIGHT (17 + i) END.
bsm sss stop.
-
bsm sss POP 1 with CURR (8 + i) (5 + i) [].
destruct r.
+
bsm sss POP 1 with RIGHT (14 + i) (12 + i) rs.
bsm sss PUSH with CURR true.
bsm sss PUSH with LEFT true.
bsm sss POP empty with ZERO END END.
bsm sss stop.
+
bsm sss POP 0 with RIGHT (14 + i) (12 + i) rs.
bsm sss PUSH with CURR false.
bsm sss PUSH with LEFT true.
bsm sss POP empty with ZERO END END.
bsm sss stop.
-
bsm sss POP 0 with CURR (8 + i) (5 + i) [].
destruct r.
+
bsm sss POP 1 with RIGHT (21 + i) (19 + i) rs.
bsm sss PUSH with CURR true.
bsm sss PUSH with LEFT false.
bsm sss POP empty with ZERO END END.
bsm sss stop.
+
bsm sss POP 0 with RIGHT (21 + i) (19 + i) rs.
bsm sss PUSH with CURR false.
bsm sss PUSH with LEFT false.
bsm sss stop.
-
bsm sss POP empty with CURR (8 + i) (5 + i).
destruct r.
+
bsm sss POP 1 with RIGHT (17 + i) END rs.
bsm sss PUSH with CURR true.
bsm sss POP empty with ZERO END END.
bsm sss stop.
+
bsm sss POP 0 with RIGHT (17 + i) END rs.
bsm sss PUSH with CURR false.
bsm sss POP empty with ZERO END END.
bsm sss stop.
