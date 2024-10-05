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
Admitted.

Theorem msg_lift_prop : forall P, (forall net, refined_raft_intermediate_reachable net -> P net) -> (forall net, msg_refined_raft_intermediate_reachable net -> P (mgv_deghost net)).
Proof using.
intros.
Admitted.

Lemma step_failure_star_raft_intermediate_reachable_extend : forall f net f' net' tr, @step_failure_star _ _ raft_msg_refined_failure_params (f, net) (f', net') tr -> msg_refined_raft_intermediate_reachable net -> msg_refined_raft_intermediate_reachable net'.
Proof using.
intros.
prep_induction H.
induction H using refl_trans_1n_trace_n1_ind; intros; subst.
-
find_inversion.
auto.
-
destruct x'.
simpl in *.
eapply MRRIR_step_failure; [|eauto].
Admitted.

Lemma map_subset : forall A B (f : A -> B) l l', (forall x, In x (map f l') -> In x (map f l)) -> exists l'', map f l' = map f l'' /\ (forall x, In x l'' -> In x l).
Proof using raft_params one_node_params orig_base_params.
induction l'; simpl; intros.
-
exists nil.
simpl in *.
intuition.
-
assert (exists x, In x l /\ f x = f a).
{
specialize (H (f a)).
concludes.
find_apply_lem_hyp in_map_iff.
firstorder.
}
specialize (IHl' ltac:(intuition)).
repeat break_exists.
break_and.
exists (x :: x0).
simpl.
Admitted.

Lemma mgv_deghost_packet_mgv_ghost_packet_partial_inverses : forall p, (@mgv_deghost_packet _ _ ghost_log_params (mgv_ghost_packet p)) = p.
Proof using.
intros.
unfold mgv_deghost_packet, mgv_ghost_packet.
simpl.
Admitted.

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
Admitted.

Theorem msg_lower_prop : forall P : _ -> Prop, (forall net, msg_refined_raft_intermediate_reachable net -> P (mgv_deghost net)) -> (forall net, refined_raft_intermediate_reachable net -> P net).
Proof using.
intros.
find_apply_lem_hyp simulation_2.
break_exists.
intuition.
subst.
Admitted.

Lemma deghost_spec : forall (net : @network _ raft_msg_refined_multi_params) h, nwState (mgv_deghost net) h = (nwState net h).
Proof using.
intros.
Admitted.

Theorem lift_prop_all_the_way : forall (P : _ -> Prop), (forall net, raft_intermediate_reachable net -> P net) -> (forall (net : @network _ raft_msg_refined_multi_params), msg_refined_raft_intermediate_reachable net -> P (deghost (mgv_deghost net))).
Proof using rri.
intros.
find_eapply_lem_hyp msg_lift_prop; eauto.
Admitted.

Theorem lower_prop_all_the_way : forall P : _ -> Prop, (forall (net : @network _ raft_msg_refined_multi_params), msg_refined_raft_intermediate_reachable net -> P (deghost (mgv_deghost net))) -> (forall net, raft_intermediate_reachable net -> P net).
Proof using rri.
intros.
eapply lower_prop; eauto.
intros.
pose proof msg_lower_prop (fun n => P (deghost n)).
simpl in *.
Admitted.

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
