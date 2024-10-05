Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss compiler_correction.
From Undecidability.MinskyMachines.MMA Require Import mma_defs mma_utils.
Set Implicit Arguments.
Set Default Proof Using "Type".
Tactic Notation "rew" "length" := autorewrite with length_db.
Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).
Local Notation "P //ₐ s -+> t" := (sss_progress (@mma_sss _) P s t) (at level 70, no associativity).
Local Notation "P //ₐ s ->> t" := (sss_compute (@mma_sss _) P s t) (at level 70, no associativity).
Local Notation "P //ₐ s ~~> t" := (sss_output (@mma_sss _) P s t) (at level 70, no associativity).
Local Notation "P //ₐ s ↓" := (sss_terminates (@mma_sss _) P s) (at level 70, no associativity).
Section mma_sim.
Variables (n : nat).
Definition mma_instr_compile lnk (_ : nat) (ii : mm_instr (pos n)) := match ii with | INCₐ k => INCₐ k :: nil | DECₐ k j => DECₐ k (lnk j) :: nil end.
Definition mma_instr_compile_length (ii : mm_instr (pos n)) := 1.
Fact mma_instr_compile_length_eq lnk i ii : length (mma_instr_compile lnk i ii) = mma_instr_compile_length ii.
Proof.
destruct ii; simpl; auto.
Fact mma_instr_compile_length_geq ii : 1 <= mma_instr_compile_length ii.
Proof.
cbv; lia.
Hint Resolve mma_instr_compile_length_eq mma_instr_compile_length_geq : core.
Hint Resolve subcode_refl : core.
Hint Resolve mma_instr_compile_sound : core.
Section mma_sim.
Variable (iP : nat) (cP : list (mm_instr (pos n))).
Local Definition lnk_Q_pair := @gen_compiler_correction _ _ _ _ mma_instr_compile_length_eq _ _ _ _ (@mma_sss_total_ni _) (@mma_sss_fun _) _ mma_instr_compile_sound (iP,cP) 1.
Local Definition lnk := projT1 lnk_Q_pair.
Local Definition Q := proj1_sig (projT2 lnk_Q_pair).
Local Lemma Hlnk : fst Q = 1 /\ lnk iP = 1 /\ forall i, out_code i (iP,cP) -> lnk i = code_end Q.
Proof.
repeat split; apply (proj2_sig (projT2 lnk_Q_pair)).
Infix "⋈" := (@eq (vec nat n)) (at level 70, no associativity).
Local Lemma HQ1 : forall i1 v1 w1 i2 v2, v1 ⋈ w1 /\ (iP,cP) //ₐ (i1,v1) ~~> (i2,v2) -> exists w2, v2 ⋈ w2 /\ Q //ₐ (lnk i1,w1) ~~> (lnk i2,w2).
Proof.
apply (proj2_sig (projT2 lnk_Q_pair)).
Local Lemma HQ1' i1 v1 i2 v2 : (iP,cP) //ₐ (i1,v1) ~~> (i2,v2) -> Q //ₐ (lnk i1,v1) ~~> (lnk i2,v2).
Proof.
intros H; destruct (@HQ1 i1 v1 v1 i2 v2) as (w2 & <- & ?); auto.
Local Lemma HQ2 : forall i1 v1 w1 j2 w2, v1 ⋈ w1 /\ Q //ₐ (lnk i1,w1) ~~> (j2,w2) -> exists i2 v2, v2 ⋈ w2 /\ (iP,cP) //ₐ (i1,v1) ~~> (i2,v2) /\ j2 = lnk i2.
Proof.
apply (proj2_sig (projT2 lnk_Q_pair)).
Local Lemma HQ2' i1 v1 j2 v2 : Q //ₐ (lnk i1,v1) ~~> (j2,v2) -> exists i2, (iP,cP) //ₐ (i1,v1) ~~> (i2,v2) /\ j2 = lnk i2.
Proof.
intros H; destruct (@HQ2 i1 v1 v1 j2 v2) as (i2 & ? & <- & ? & ->); auto.
exists i2; auto.
Variable v : vec nat n.
Local Lemma Q_spec1 : (iP,cP) //ₐ (iP,v) ↓ -> exists w', Q //ₐ (1,v) ~~> (code_end Q, w').
Proof.
intros ((i1,v1) & H1).
exists v1.
rewrite <- (proj2 (proj2 Hlnk) i1), <- (proj1 (proj2 Hlnk)); auto using HQ1'.
destruct H1; auto.
Local Lemma Q_spec2 : Q //ₐ (1,v) ↓ -> (iP,cP) //ₐ (iP,v) ↓.
Proof.
intros ((j,w2) & H1).
rewrite <- (proj1 (proj2 Hlnk)) in H1.
destruct HQ2' with (1 := H1) as (i2 & ? & ->).
exists (i2,w2); auto.
Definition mma_sim := snd Q.
Definition mma_sim_end := code_end Q.
End mma_sim.
End mma_sim.
Section mma2_simul.
Variable (iP : nat) (cP : list (mm_instr (pos 2))).
Let Q := mma_sim iP cP.
Local Definition eQ := 1+length Q.
Local Definition cN : list (mm_instr (pos 2)) := mma_null pos0 eQ ++ mma_null pos1 (1+eQ) ++ mma_jump 0 pos0.
Local Definition L1 := @mma_null_length 2 pos0 eQ.
Local Definition L2 := @mma_null_length 2 pos1 (1+eQ).
Let N_spec v : (eQ,cN) //ₐ (eQ,v) -+> (0,vec_zero).
Proof.
unfold cN.
apply sss_progress_trans with (1+eQ,v[0/pos0]).
1: {
apply subcode_sss_progress with (P := (eQ,mma_null pos0 eQ)); auto.
apply mma_null_progress; auto.
}
apply sss_progress_trans with (2+eQ,(v[0/pos0])[0/pos1]).
1: {
pose proof L1 as L1.
apply subcode_sss_progress with (P := (1+eQ,mma_null pos1 (1+eQ))); auto.
apply mma_null_progress; auto.
}
replace ((v[0/pos0])[0/pos1]) with (@vec_zero 2).
2: {
apply vec_pos_ext; intros p.
repeat (invert pos p; rew vec).
}
pose proof L1 as L1.
pose proof L2 as L2.
apply subcode_sss_progress with (P := (2+eQ,mma_jump 0 pos0)); auto.
apply mma_jump_progress; auto.
Definition mma2_simul := Q ++ cN.
Let cQ_sim : (1,Q) <sc (1,mma2_simul).
Proof.
unfold mma2_simul; auto.
Let cN_sim : (eQ,cN) <sc (1,mma2_simul).
Proof.
unfold mma2_simul, eQ; auto.
End mma2_simul.

Fact mma_instr_compile_length_eq lnk i ii : length (mma_instr_compile lnk i ii) = mma_instr_compile_length ii.
Proof.
destruct ii; simpl; auto.
