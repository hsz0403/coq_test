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

Theorem msg_refined_raft_net_invariant : forall P net, msg_refined_raft_net_invariant_init P -> msg_refined_raft_net_invariant_client_request P -> msg_refined_raft_net_invariant_timeout P -> msg_refined_raft_net_invariant_append_entries P -> msg_refined_raft_net_invariant_append_entries_reply P -> msg_refined_raft_net_invariant_request_vote P -> msg_refined_raft_net_invariant_request_vote_reply P -> msg_refined_raft_net_invariant_do_leader P -> msg_refined_raft_net_invariant_do_generic_server P -> msg_refined_raft_net_invariant_state_same_packet_subset P -> msg_refined_raft_net_invariant_reboot P -> msg_refined_raft_intermediate_reachable net -> P net.
Proof using.
intros.
induction H10.
-
intuition.
-
match goal with [H : step_failure _ _ _ |- _ ] => invcs H end.
+
unfold mgv_refined_net_handlers in *.
simpl in *.
unfold refined_net_handlers in *.
simpl in *.
unfold RaftNetHandler in *.
repeat break_let.
repeat find_inversion.
remember (update_elections_data_net (pDst p) (pSrc p) (snd (pBody p)) (nwState net (pDst p))) as post_ghost_state.
assert (msg_refined_raft_intermediate_reachable {| nwPackets := (xs ++ ys) ++ send_packets (pDst p) (@add_ghost_msg _ _ ghost_log_params (pDst p) (post_ghost_state, r0) l4); nwState := update name_eq_dec (nwState net) (pDst p) (post_ghost_state, r0) |}) by (subst; eapply MRRIR_handleMessage; eauto; in_crush).
assert (msg_refined_raft_intermediate_reachable {| nwPackets := (xs ++ ys) ++ send_packets (pDst p) (@add_ghost_msg _ _ ghost_log_params (pDst p) (post_ghost_state, r0) l4) ++ send_packets (pDst p) (@add_ghost_msg _ _ ghost_log_params (pDst p) (post_ghost_state, r1) l5); nwState := update name_eq_dec (nwState net) (pDst p) (post_ghost_state, r1) |}) by (eapply MRRIR_doLeader; eauto; try solve [in_crush]; simpl in *; intros; repeat break_if; try congruence; auto).
subst.
eapply_prop msg_refined_raft_net_invariant_do_generic_server.
eauto.
eapply_prop msg_refined_raft_net_invariant_do_leader.
eauto.
eapply msg_refined_raft_invariant_handle_message with (P := P); eauto using in_app_or.
auto.
simpl.
break_if; intuition eauto.
eauto.
simpl.
eapply in_app_or.
simpl.
{
clear H11.
match goal with | H : msg_refined_raft_intermediate_reachable ?net |- msg_refined_raft_intermediate_reachable ?net' => assert (net = net') end.
simpl.
f_equal; auto.
-
repeat rewrite app_ass.
auto.
-
apply functional_extensionality.
intros.
repeat break_if; simpl; auto.
-
repeat find_rewrite; auto.
}
simpl in *.
break_if; eauto; congruence.
simpl in *.
intros.
repeat break_if; auto.
intros.
simpl in *.
in_crush.
unfold add_ghost_msg in *.
do_in_map.
subst.
do_in_app.
intuition; try do_in_app; intuition.
*
left.
apply in_app_iff.
left.
apply in_app_iff.
right.
simpl in *.
rewrite map_map.
apply in_map_iff.
eexists; intuition; eauto.
simpl in *.
f_equal.
f_equal.
unfold write_ghost_log.
simpl.
find_apply_lem_hyp doGenericServer_log.
find_apply_lem_hyp doLeader_log.
repeat find_rewrite.
auto.
*
left.
apply in_app_iff.
right.
simpl in *.
rewrite map_map.
apply in_map_iff.
eexists; intuition; eauto.
simpl in *.
f_equal.
f_equal.
unfold write_ghost_log.
simpl.
find_apply_lem_hyp doGenericServer_log.
find_apply_lem_hyp doLeader_log.
repeat find_rewrite.
auto.
*
right.
simpl in *.
rewrite map_map.
apply in_map_iff.
eexists; intuition; eauto.
+
unfold mgv_refined_input_handlers in *.
simpl in *.
unfold refined_input_handlers in *.
simpl in *.
unfold RaftInputHandler in *.
repeat break_let.
repeat find_inversion.
remember (update_elections_data_input h inp (nwState net h)) as post_ghost_state.
assert (msg_refined_raft_intermediate_reachable {| nwPackets := (nwPackets net) ++ send_packets h (@add_ghost_msg _ _ ghost_log_params h (post_ghost_state, r0) l4); nwState := update name_eq_dec (nwState net) h (post_ghost_state, r0) |}) by (subst; eapply MRRIR_handleInput; eauto; in_crush).
assert (msg_refined_raft_intermediate_reachable {| nwPackets := (nwPackets net) ++ send_packets h (@add_ghost_msg _ _ ghost_log_params h (post_ghost_state, r0) l4) ++ send_packets h (@add_ghost_msg _ _ ghost_log_params h (post_ghost_state, r1) l6); nwState := update name_eq_dec (nwState net) h (post_ghost_state, r1) |}) by (eapply MRRIR_doLeader; eauto; try solve [in_crush]; simpl in *; intros; repeat break_if; try congruence; auto).
subst.
eapply_prop msg_refined_raft_net_invariant_do_generic_server.
eauto.
eapply_prop msg_refined_raft_net_invariant_do_leader.
eauto.
eapply msg_refined_raft_invariant_handle_input with (P := P); eauto using in_app_or.
auto.
simpl.
break_if; intuition eauto.
eauto.
simpl.
eapply in_app_or.
simpl.
{
clear H11.
match goal with | H : msg_refined_raft_intermediate_reachable ?net |- msg_refined_raft_intermediate_reachable ?net' => assert (net = net') end.
simpl.
f_equal; auto.
-
repeat rewrite app_ass.
auto.
-
apply functional_extensionality.
intros.
repeat break_if; simpl; auto.
-
repeat find_rewrite; auto.
}
simpl in *.
break_if; eauto; congruence.
simpl in *.
intros.
repeat break_if; auto.
intros.
simpl in *.
in_crush.
unfold add_ghost_msg in *.
do_in_map.
subst.
do_in_app.
intuition; try do_in_app; intuition.
*
left.
apply in_app_iff.
left.
apply in_app_iff.
right.
simpl in *.
rewrite map_map.
apply in_map_iff.
eexists; intuition; eauto.
simpl in *.
f_equal.
f_equal.
unfold write_ghost_log.
simpl.
find_apply_lem_hyp doGenericServer_log.
find_apply_lem_hyp doLeader_log.
repeat find_rewrite.
auto.
*
left.
apply in_app_iff.
right.
simpl in *.
rewrite map_map.
apply in_map_iff.
eexists; intuition; eauto.
simpl in *.
f_equal.
f_equal.
unfold write_ghost_log.
simpl.
find_apply_lem_hyp doGenericServer_log.
find_apply_lem_hyp doLeader_log.
repeat find_rewrite.
auto.
*
right.
simpl in *.
rewrite map_map.
apply in_map_iff.
eexists; intuition; eauto.
+
match goal with | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] => assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) -> In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush) end.
eapply_prop msg_refined_raft_net_invariant_state_same_packet_subset; [|eauto|idtac|]; eauto.
+
match goal with | [ H : nwPackets ?net = _ |- _ {| nwPackets := ?ps ; nwState := ?st |} ] => assert (forall p, In p (nwPackets {| nwPackets := ps ; nwState := st |}) -> In p (nwPackets net)) by (intros; simpl in *; find_rewrite; in_crush) end.
eapply_prop msg_refined_raft_net_invariant_state_same_packet_subset; [|eauto|idtac|]; eauto.
+
auto.
+
eapply_prop msg_refined_raft_net_invariant_reboot; eauto; intros; simpl in *; repeat break_if; intuition; subst; intuition eauto.
destruct (nwState net h); auto.
-
eapply msg_refined_raft_invariant_handle_input; eauto.
-
eapply msg_refined_raft_invariant_handle_message; eauto.
-
eapply_prop msg_refined_raft_net_invariant_do_leader; eauto.
-
eapply_prop msg_refined_raft_net_invariant_do_generic_server; eauto.
