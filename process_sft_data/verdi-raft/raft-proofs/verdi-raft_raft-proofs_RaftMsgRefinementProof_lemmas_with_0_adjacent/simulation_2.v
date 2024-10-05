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

Theorem simulation_2 : forall net, refined_raft_intermediate_reachable net -> exists rnet, net = mgv_deghost rnet /\ msg_refined_raft_intermediate_reachable rnet.
Proof using.
intros.
induction H.
-
exists (mgv_reghost step_async_init).
intuition.
unfold mgv_reghost.
constructor.
-
break_exists.
break_and.
apply mgv_ghost_simulation_2 with (gnet := x) in H0; auto.
repeat (break_exists; intuition).
subst.
exists x0.
intuition.
eapply MRRIR_step_failure; eauto.
-
break_exists.
break_and.
subst.
assert (msg_refined_raft_intermediate_reachable ({| nwPackets := (nwPackets x) ++ (@send_packets _ raft_msg_refined_multi_params h (@add_ghost_msg _ _ ghost_log_params h (update_elections_data_input h inp (nwState (mgv_deghost x) h), d) l)); nwState := st' |})) by (unfold mgv_deghost in *; repeat break_match; simpl in *; eapply MRRIR_handleInput; repeat break_match; simpl in *; eauto; simpl in *; in_crush).
pose proof map_subset _ _ mgv_deghost_packet (nwPackets x ++ @send_packets _ raft_msg_refined_multi_params h (@add_ghost_msg _ _ ghost_log_params h (update_elections_data_input h inp (nwState (mgv_deghost x) h), d) l)) (map mgv_ghost_packet ps').
forwards.
{
intros.
rewrite map_map in *.
do_in_map.
subst.
unfold mgv_deghost_packet.
simpl in *.
find_apply_hyp_hyp.
rewrite map_app.
in_crush.
unfold add_ghost_msg.
repeat rewrite map_map.
simpl in *.
right.
in_crush.
}
concludes.
break_exists_name dps'.
intuition.
exists {| nwPackets := dps'; nwState := st' |}.
intuition.
+
rewrite map_map in H7.
rewrite map_ext with (g := id) in H7; eauto using mgv_deghost_packet_mgv_ghost_packet_partial_inverses.
rewrite map_id in *.
subst.
unfold mgv_deghost.
simpl.
auto.
+
eapply step_failure_star_raft_intermediate_reachable_extend with (f := []); eauto using step_failure_dup_drop_step.
eapply step_failure_dup_drop_step.
apply dup_drop_reorder; auto.
auto using packet_eq_dec.
-
break_exists.
break_and.
subst.
unfold mgv_deghost in *.
simpl in *.
find_apply_lem_hyp map_partition.
break_exists_name xs'.
break_exists_name p'.
break_exists_name ys'.
intuition.
subst.
simpl in *.
repeat break_match.
simpl in *.
subst.
simpl in *.
assert (msg_refined_raft_intermediate_reachable ({| nwPackets := (xs' ++ ys') ++ (@send_packets _ raft_msg_refined_multi_params (pDst p') (@add_ghost_msg _ _ ghost_log_params (pDst p') (update_elections_data_net (pDst p') (pSrc p') (snd (pBody p')) (nwState (pDst p')), d) l)); nwState := st' |})).
{
unfold mgv_deghost in *; repeat break_match; simpl in *.
eapply MRRIR_handleMessage.
eauto.
simpl.
eauto.
simpl.
eauto.
simpl.
eauto.
simpl.
auto.
simpl in *; in_crush.
}
pose proof map_subset _ _ mgv_deghost_packet ((xs' ++ ys') ++ @send_packets _ raft_msg_refined_multi_params (pDst p') (@add_ghost_msg _ _ ghost_log_params (pDst p') (update_elections_data_net (pDst p') (pSrc p') (snd (pBody p')) (nwState (pDst p')), d) l)) (map mgv_ghost_packet ps').
forwards.
{
intros.
rewrite map_map in *.
do_in_map.
subst.
unfold mgv_deghost_packet.
simpl in *.
find_apply_hyp_hyp.
rewrite map_app.
in_crush.
-
left.
apply in_map_iff.
eexists; intuition; eauto.
-
left.
apply in_map_iff.
eexists; intuition; eauto.
-
right.
unfold add_ghost_msg.
repeat rewrite map_map.
simpl in *.
in_crush.
}
concludes.
break_exists_name dps'.
intuition.
exists {| nwPackets := dps'; nwState := st' |}.
intuition.
+
rewrite map_map in H7.
rewrite map_ext with (g := id) in H7; eauto using mgv_deghost_packet_mgv_ghost_packet_partial_inverses.
rewrite map_id in *.
subst.
unfold mgv_deghost.
simpl.
auto.
+
eapply step_failure_star_raft_intermediate_reachable_extend with (f := []); eauto using step_failure_dup_drop_step.
eapply step_failure_dup_drop_step.
apply dup_drop_reorder; auto.
auto using packet_eq_dec.
-
break_exists.
break_and.
subst.
assert (msg_refined_raft_intermediate_reachable ({| nwPackets := (nwPackets x) ++ (@send_packets _ raft_msg_refined_multi_params h (@add_ghost_msg _ _ ghost_log_params h (gd, d') ms)); nwState := st' |})).
{
unfold mgv_deghost in *; repeat break_match; simpl in *.
eapply MRRIR_doLeader; repeat break_match; simpl in *; eauto; simpl in *; in_crush.
}
pose proof map_subset _ _ mgv_deghost_packet (nwPackets x ++ @send_packets _ raft_msg_refined_multi_params h (@add_ghost_msg _ _ ghost_log_params h (gd, d') ms)) (map mgv_ghost_packet ps').
forwards.
{
intros.
rewrite map_map in *.
do_in_map.
subst.
unfold mgv_deghost_packet.
simpl in *.
find_apply_hyp_hyp.
rewrite map_app.
in_crush.
unfold add_ghost_msg.
repeat rewrite map_map.
simpl in *.
right.
in_crush.
}
concludes.
break_exists_name dps'.
intuition.
exists {| nwPackets := dps'; nwState := st' |}.
intuition.
+
rewrite map_map in H8.
rewrite map_ext with (g := id) in H8; eauto using mgv_deghost_packet_mgv_ghost_packet_partial_inverses.
rewrite map_id in *.
subst.
unfold mgv_deghost.
simpl.
auto.
+
eapply step_failure_star_raft_intermediate_reachable_extend with (f := []); eauto using step_failure_dup_drop_step.
eapply step_failure_dup_drop_step.
apply dup_drop_reorder; auto.
auto using packet_eq_dec.
-
break_exists.
break_and.
subst.
assert (msg_refined_raft_intermediate_reachable ({| nwPackets := (nwPackets x) ++ (@send_packets _ raft_msg_refined_multi_params h (@add_ghost_msg _ _ ghost_log_params h (gd, d') ms)); nwState := st' |})).
{
unfold mgv_deghost in *; repeat break_match; simpl in *.
eapply MRRIR_doGenericServer; repeat break_match; simpl in *; eauto; simpl in *; in_crush.
}
pose proof map_subset _ _ mgv_deghost_packet (nwPackets x ++ @send_packets _ raft_msg_refined_multi_params h (@add_ghost_msg _ _ ghost_log_params h (gd, d') ms)) (map mgv_ghost_packet ps').
forwards.
{
intros.
rewrite map_map in *.
do_in_map.
subst.
unfold mgv_deghost_packet.
simpl in *.
find_apply_hyp_hyp.
rewrite map_app.
in_crush.
unfold add_ghost_msg.
repeat rewrite map_map.
simpl in *.
right.
in_crush.
}
concludes.
break_exists_name dps'.
intuition.
exists {| nwPackets := dps'; nwState := st' |}.
intuition.
+
rewrite map_map in H8.
rewrite map_ext with (g := id) in H8; eauto using mgv_deghost_packet_mgv_ghost_packet_partial_inverses.
rewrite map_id in *.
subst.
unfold mgv_deghost.
simpl.
auto.
+
eapply step_failure_star_raft_intermediate_reachable_extend with (f := []); eauto using step_failure_dup_drop_step.
eapply step_failure_dup_drop_step.
apply dup_drop_reorder; auto.
auto using packet_eq_dec.
