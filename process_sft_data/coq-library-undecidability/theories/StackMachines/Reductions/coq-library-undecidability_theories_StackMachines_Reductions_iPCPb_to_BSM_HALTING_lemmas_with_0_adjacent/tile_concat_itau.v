Require Import List Arith Lia.
Import ListNotations.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.Shared.Libs.DLW Require Import utils list_bool pos vec subcode sss.
From Undecidability.StackMachines.BSM Require Import tiles_solvable bsm_defs bsm_utils bsm_pcp.
From Undecidability.PCP Require Import PCP PCP_facts.
Set Default Proof Using "Type".
Fact tile_concat_itau ln lt : tile_concat ln lt = (itau1 lt (rev ln), itau2 lt (rev ln)).
Proof.
induction ln as [ | i ln IH ]; simpl; auto.
rewrite itau1_app, itau2_app; simpl.
unfold card, string; generalize (nth i lt ([], [])); intros (a,b); rewrite IH.
repeat rewrite <- app_nil_end; auto.
Local Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).
Local Notation "P // s ~~> t" := (sss_output (@bsm_sss _) P s t).
Local Notation "P // s ↓" := (sss_terminates (@bsm_sss _) P s).
Section iPCPb_to_BSM_HALTING.
Let f (lt : list (card bool)) : BSM_PROBLEM.
Proof.
exists 4, 1, (pcp_bsm lt).
exact (vec_set_pos (fun _ => nil)).
Defined.
Goal forall x, length(pcp_bsm x) >= 80.
Proof.
intros; rewrite pcp_bsm_size; lia.
End iPCPb_to_BSM_HALTING.

Fact tile_concat_itau ln lt : tile_concat ln lt = (itau1 lt (rev ln), itau2 lt (rev ln)).
Proof.
induction ln as [ | i ln IH ]; simpl; auto.
rewrite itau1_app, itau2_app; simpl.
unfold card, string; generalize (nth i lt ([], [])); intros (a,b); rewrite IH.
repeat rewrite <- app_nil_end; auto.
