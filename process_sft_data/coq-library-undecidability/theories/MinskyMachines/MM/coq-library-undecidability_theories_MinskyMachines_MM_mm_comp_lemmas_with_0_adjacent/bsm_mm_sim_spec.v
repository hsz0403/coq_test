Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import utils list_bool pos vec subcode sss compiler_correction.
From Undecidability.StackMachines.BSM Require Import bsm_defs.
From Undecidability.MinskyMachines.MM Require Import mm_defs mm_utils.
Set Implicit Arguments.
Set Default Proof Using "Type".
Tactic Notation "rew" "length" := autorewrite with length_db.
Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).
Local Notation "I '/BSM/' s -1> t" := (bsm_sss I s t) (at level 70, no associativity).
Local Notation "P '/BSM/' s -+> t" := (sss_progress (@bsm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/BSM/' s ->> t" := (sss_compute (@bsm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/BSM/' s ~~> t" := (sss_output (@bsm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/BSM/' s ↓" := (sss_terminates (@bsm_sss _) P s)(at level 70, no associativity).
Local Notation "P '/MM/' s -+> t" := (sss_progress (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/MM/' s ->> t" := (sss_compute (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/MM/' s '~~>' t" := (sss_output (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/MM/' s ↓" := (sss_terminates (@mm_sss _) P s)(at level 70, no associativity).
Section simulator.
Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew vec.
Variables (m : nat).
Let n := 2+m.
Local Definition tmp1 : pos n := pos0.
Local Definition tmp2 : pos n := pos1.
Local Definition reg p: pos n := pos_nxt (pos_nxt p).
Local Lemma Hv12 : tmp1 <> tmp2.
Proof.
discriminate.
Local Lemma Hvr1 : forall p, reg p <> tmp1.
Proof.
discriminate.
Local Lemma Hvr2 : forall p, reg p <> tmp2.
Proof.
discriminate.
Let Hreg : forall p q, reg p = reg q -> p = q.
Proof.
intros; do 2 apply pos_nxt_inj; apply H.
Definition bsm_state_enc (v : vec (list bool) m) w := w#>tmp1 = 0 /\ w#>tmp2 = 0 /\ forall p, w#>(reg p) = stack_enc (v#>p).
Definition bsm_instr_compile lnk i ii := match ii with | PUSH s Zero => mm_push_Zero (reg s) tmp1 tmp2 (lnk i) | PUSH s One => mm_push_One (reg s) tmp1 tmp2 (lnk i) | POP s j k => mm_pop (reg s) tmp1 tmp2 (lnk i) (lnk j) (lnk (1+i)) (lnk k) end.
Definition bsm_instr_compile_length (ii : bsm_instr m) := match ii with | PUSH _ Zero => 7 | PUSH _ One => 8 | POP _ _ _ => 16 end.
Fact bsm_instr_compile_length_eq lnk i ii : length (bsm_instr_compile lnk i ii) = bsm_instr_compile_length ii.
Proof.
destruct ii as [ | ? [] ]; simpl; auto.
Fact bsm_instr_compile_length_geq ii : 1 <= bsm_instr_compile_length ii.
Proof.
destruct ii as [ | ? [] ]; simpl; auto; lia.
Hint Resolve bsm_instr_compile_length_eq bsm_instr_compile_length_geq : core.
Hint Resolve bsm_instr_compile_sound : core.
Section bsm_sim.
Variable (iP : nat) (cP : list (bsm_instr m)).
Local Definition lnk_Q_pair := @gen_compiler_correction _ _ _ _ bsm_instr_compile_length_eq _ _ _ _ (@bsm_sss_total' _) (@mm_sss_fun _) _ bsm_instr_compile_sound (iP,cP) 1.
Local Definition lnk := projT1 lnk_Q_pair.
Local Definition Q := proj1_sig (projT2 lnk_Q_pair).
Local Lemma Hlnk : fst Q = 1 /\ lnk iP = 1 /\ forall i, out_code i (iP,cP) -> lnk i = code_end Q.
Proof.
repeat split; apply (proj2_sig (projT2 lnk_Q_pair)).
Infix "⋈" := bsm_state_enc (at level 70, no associativity).
Local Lemma HQ1 : forall i1 v1 w1 i2 v2, v1 ⋈ w1 /\ (iP,cP) /BSM/ (i1,v1) ~~> (i2,v2) -> exists w2, v2 ⋈ w2 /\ Q /MM/ (lnk i1,w1) ~~> (lnk i2,w2).
Proof.
apply (proj2_sig (projT2 lnk_Q_pair)).
Local Lemma HQ2 : forall i1 v1 w1 j2 w2, v1 ⋈ w1 /\ Q /MM/ (lnk i1,w1) ~~> (j2,w2) -> exists i2 v2, v2 ⋈ w2 /\ (iP,cP) /BSM/ (i1,v1) ~~> (i2,v2) /\ j2 = lnk i2.
Proof.
apply (proj2_sig (projT2 lnk_Q_pair)).
Variable v : vec (list bool) m.
Local Definition w := 0##0##vec_map stack_enc v.
Let w_prop : bsm_state_enc v w.
Proof.
red; unfold w, tmp1, tmp2; repeat split; rew vec.
intros p; unfold reg; simpl.
rewrite vec_pos_map; trivial.
Local Lemma Q_spec1 : (iP,cP) /BSM/ (iP,v) ↓ -> exists w', Q /MM/ (1,w) ~~> (code_end Q, w') /\ w'#>tmp1 = 0 /\ w'#>tmp2 = 0.
Proof.
intros ((i1,v1) & H1).
destruct HQ1 with (1 := conj w_prop H1) as (w' & H2 & H3).
rewrite <- (proj2 (proj2 Hlnk) i1), <- (proj1 (proj2 Hlnk)).
*
exists w'; split; auto; red in H2; tauto.
*
apply H1.
Local Lemma Q_spec2 : Q /MM/ (1,w) ↓ -> (iP,cP) /BSM/ (iP,v) ↓.
Proof.
intros ((j,w2) & H1).
rewrite <- (proj1 (proj2 Hlnk)) in H1.
destruct HQ2 with (1 := conj w_prop H1) as (i2 & v2 & H2 & H3 & _).
exists (i2,v2); auto.
Local Definition bsm_mm_sim := snd Q.
Local Definition iE := code_end Q.
Local Definition cN := mm_nullify tmp1 iE (map (fun p => pos_nxt (pos_nxt p)) (pos_list m)).
Local Definition cE := cN ++ DEC tmp1 0 :: nil.
Local Lemma E_spec w' : w'#>tmp1 = 0 -> w'#>tmp2 = 0 -> (iE,cE) /MM/ (iE,w') -+> (0,vec_zero).
Proof.
intros H1 H2.
unfold cE.
apply sss_compute_progress_trans with (length cN+iE,vec_zero).
+
apply subcode_sss_compute with (P := (iE,cN)); auto.
apply mm_nullify_compute; auto.
*
intros p Hp.
apply in_map_iff in Hp.
destruct Hp as (x & H3 & H4); subst; discriminate.
*
intros p Hp.
apply in_map_iff in Hp.
destruct Hp as (x & H3 & H4); subst; apply vec_zero_spec.
*
intros p Hp.
unfold n, tmp1, tmp2 in *; simpl in p.
pos_inv p; auto.
pos_inv p; auto.
destruct Hp; apply in_map_iff; exists p; split; auto.
apply pos_list_prop.
+
apply subcode_sss_progress with (P := (length cN+iE,DEC tmp1 0::nil)); auto.
mm sss DEC 0 with tmp1 0.
apply subcode_refl.
mm sss stop.
Definition bsm_mm := snd Q ++ cE.
Let cQ_sim : Q <sc (1,bsm_mm).
Proof.
pose proof Hlnk as Hlnk.
unfold bsm_mm; destruct Q as (iQ,cQ); simpl in Hlnk.
simpl snd; rewrite (proj1 Hlnk); auto.
Let cE_sim : (iE,cE) <sc (1,bsm_mm).
Proof.
unfold iE, bsm_mm; subcode_tac; solve list eq.
rewrite (proj1 Hlnk); auto.
End bsm_sim.
End simulator.

Theorem bsm_mm_sim_spec : (iP,cP) /BSM/ (iP,v) ↓ <-> (1,bsm_mm_sim) /MM/ (1,w) ↓.
Proof.
rewrite <- (proj1 Hlnk) at 1.
rewrite <- surjective_pairing.
split; auto using Q_spec2.
intros H.
destruct (Q_spec1 H) as (w' & H1 & _).
exists (code_end Q, w'); auto.
