Require Import FunctionalExtensionality.
Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import Verdi.DupDropReordering.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RaftMsgRefinementInterface.
Section RaftMsgRefinement.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Ltac workhorse := try match goal with | [ |- mkNetwork _ _ = mkNetwork _ _ ] => f_equal end; try match goal with | [ |- (fun _ => _) = (fun _ => _) ] => apply functional_extensionality; intros end; repeat break_match; repeat match goal with | [ H : (_, _) = (_, _) |- _ ] => invc H end; repeat (simpl in *; subst); repeat rewrite map_app; repeat rewrite map_map.
Notation mgv_deghost := (@mgv_deghost _ _ ghost_log_params).
Context {rri : raft_refinement_interface}.
Instance rmri : raft_msg_refinement_interface.
Proof.
split.
-
exact msg_refined_raft_net_invariant.
-
exact msg_refined_raft_net_invariant'.
-
exact msg_lift_prop.
-
exact lift_prop_all_the_way.
-
exact msg_lower_prop.
-
exact lower_prop_all_the_way.
-
exact deghost_spec.
-
exact simulation_1.
End RaftMsgRefinement.

Theorem simulation_1 : forall net, msg_refined_raft_intermediate_reachable net -> refined_raft_intermediate_reachable (mgv_deghost net).
Proof using.
intros.
induction H.
-
constructor.
-
simpl in *.
pose proof (RRIR_step_failure).
specialize (H1 failed (mgv_deghost net) failed' (mgv_deghost net') out).
apply H1; auto.
apply (@mgv_ghost_simulation_1 _ _ _ ghost_log_params); auto.
-
unfold mgv_deghost in *.
simpl in *.
eapply RRIR_handleInput; eauto.
+
simpl in *.
repeat break_match.
simpl in *.
eauto.
+
intros.
simpl in *.
repeat break_match; subst; simpl in *; repeat find_higher_order_rewrite; break_if; subst; simpl in *; congruence.
+
intros.
simpl in *.
in_crush.
find_apply_hyp_hyp.
in_crush.
right.
unfold add_ghost_msg in *.
do_in_map.
subst.
simpl in *.
apply in_map_iff.
eauto.
-
unfold mgv_deghost in *.
simpl in *.
pose proof (RRIR_handleMessage).
specialize (H5 (@mkPacket _ raft_refined_multi_params (pSrc p) (pDst p) (snd (pBody p)))).
eapply H5; eauto.
+
simpl in *.
repeat break_match.
simpl in *.
repeat find_rewrite.
eauto.
+
simpl in *.
unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params, raft_msg_refined_multi_params, raft_refined_multi_params in *.
simpl in *.
unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params, raft_msg_refined_multi_params, raft_refined_multi_params in *.
simpl in *.
repeat find_rewrite.
map_crush.
eauto.
+
intros.
repeat break_match.
simpl in *.
repeat find_higher_order_rewrite.
repeat break_match; congruence.
+
in_crush.
find_apply_hyp_hyp.
in_crush.
right.
unfold add_ghost_msg in *.
do_in_map.
subst.
simpl in *.
apply in_map_iff.
eauto.
-
unfold mgv_deghost in *.
simpl in *.
eapply RRIR_doLeader; eauto.
+
simpl in *.
repeat break_match.
simpl in *.
eauto.
+
simpl in *.
intros.
repeat break_match; simpl in *; repeat find_higher_order_rewrite; repeat break_match; congruence.
+
in_crush.
find_apply_hyp_hyp.
in_crush.
right.
unfold add_ghost_msg in *.
do_in_map.
subst.
simpl in *.
apply in_map_iff.
eauto.
-
unfold mgv_deghost in *.
simpl in *.
eapply RRIR_doGenericServer; eauto.
+
simpl in *.
repeat break_match.
simpl in *.
eauto.
+
simpl in *.
intros.
repeat break_match; simpl in *; repeat find_higher_order_rewrite; repeat break_match; congruence.
+
in_crush.
find_apply_hyp_hyp.
in_crush.
right.
unfold add_ghost_msg in *.
do_in_map.
subst.
simpl in *.
apply in_map_iff.
eauto.
