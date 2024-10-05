Require Import FunctionalExtensionality.
Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Set Bullet Behavior "Strict Subproofs".
Section RaftRefinementProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Ltac workhorse := try match goal with | [ |- mkNetwork _ _ = mkNetwork _ _ ] => f_equal end; try match goal with | [ |- (fun _ => _) = (fun _ => _) ] => apply functional_extensionality; intros end; repeat break_match; repeat match goal with | [ H : (_, _) = (_, _) |- _ ] => invc H end; repeat (simpl in *; subst); repeat rewrite map_app; repeat rewrite map_map.
Instance rri : raft_refinement_interface.
Proof.
split.
-
exact refined_raft_net_invariant.
-
exact refined_raft_net_invariant'.
-
exact lift_prop.
-
exact lower_prop.
-
exact deghost_spec.
-
exact simulation_1.
End RaftRefinementProof.
Hint Extern 4 (@BaseParams) => apply raft_refined_base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply raft_refined_multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply raft_refined_failure_params : typeclass_instances.

Theorem simulation_2 : forall net, raft_intermediate_reachable net -> exists rnet, net = deghost rnet /\ refined_raft_intermediate_reachable rnet.
Proof using.
intros.
induction H.
-
exists (reghost step_async_init).
intuition.
unfold reghost.
constructor.
-
break_exists.
break_and.
apply ghost_simulation_2 with (gnet := x) in H0; auto.
repeat (break_exists; intuition).
subst.
exists x0.
intuition.
eapply RRIR_step_failure; eauto.
-
break_exists.
break_and.
subst.
exists {| nwPackets := map ghost_packet ps' ; nwState := update name_eq_dec (nwState x) h (update_elections_data_input h inp (nwState x h), d) |}.
intuition.
+
unfold deghost.
simpl in *.
map_crush.
f_equal.
*
map_id.
*
apply functional_extensionality.
intros.
find_higher_order_rewrite.
repeat break_match; auto.
simpl in *.
congruence.
+
unfold deghost in *.
eapply RRIR_handleInput; repeat break_match; simpl in *; eauto.
simpl in *.
in_crush.
find_apply_hyp_hyp.
in_crush.
destruct x.
auto.
-
break_exists.
break_and.
subst.
exists {| nwPackets := map ghost_packet ps' ; nwState := update name_eq_dec (nwState x) (pDst p) (update_elections_data_net (pDst p) (pSrc p) (pBody p) (nwState x (pDst p)), d) |}.
intuition.
+
unfold deghost.
simpl in *.
map_crush.
f_equal.
*
map_id.
*
apply functional_extensionality.
intros.
find_higher_order_rewrite.
repeat break_match; auto.
simpl in *.
congruence.
+
unfold deghost in *.
eapply RRIR_handleMessage with (p0 := ghost_packet p); repeat break_match; simpl in *; eauto.
*
simpl in *.
match goal with | H : map _ ?la = ?lb |- _ => symmetry in H; pose proof @map_inverses _ _ la lb deghost_packet ghost_packet end.
repeat (forwards; [intro a; destruct a; reflexivity|]; concludes; match goal with | H : forall _ : packet, _ = _ |- _ => clear H end).
concludes.
map_crush.
eauto.
*
simpl in *.
in_crush.
find_apply_hyp_hyp.
in_crush.
-
break_exists.
break_and.
subst.
exists {| nwPackets := map ghost_packet ps' ; nwState := update name_eq_dec (nwState x) h (fst (nwState x h) , d') |}.
intuition.
+
unfold deghost.
simpl in *.
map_crush.
f_equal.
*
map_id.
*
apply functional_extensionality.
intros.
find_higher_order_rewrite.
repeat break_match; auto.
simpl in *.
congruence.
+
unfold deghost in *.
simpl in *.
repeat break_match; simpl in *.
eapply RRIR_doLeader with (d0 := d) (h0 := h); repeat (break_match; simpl in *); eauto.
*
simpl in *.
find_rewrite.
simpl in *.
auto.
*
simpl in *.
in_crush.
find_apply_hyp_hyp.
in_crush.
destruct x.
auto.
-
break_exists.
break_and.
subst.
exists {| nwPackets := map ghost_packet ps' ; nwState := update name_eq_dec (nwState x) h (fst (nwState x h) , d') |}.
intuition.
+
unfold deghost.
simpl in *.
map_crush.
f_equal.
*
map_id.
*
apply functional_extensionality.
intros.
find_higher_order_rewrite.
repeat break_match; auto.
simpl in *.
congruence.
+
unfold deghost in *.
simpl in *.
repeat break_match; simpl in *.
eapply RRIR_doGenericServer with (d0 := d) (h0 := h); repeat (break_match; simpl in *); eauto.
*
simpl in *.
find_rewrite.
simpl in *.
auto.
*
simpl in *.
in_crush.
find_apply_hyp_hyp.
in_crush.
destruct x.
auto.
