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

Theorem simulation_1 : forall net, refined_raft_intermediate_reachable net -> raft_intermediate_reachable (deghost net).
Proof using.
intros.
induction H.
-
constructor.
-
simpl in *.
pose proof (RIR_step_failure).
specialize (H1 failed (deghost net) failed' (deghost net') out).
apply H1; auto.
apply ghost_simulation_1; auto.
-
unfold deghost in *.
simpl in *.
eapply RIR_handleInput; eauto.
+
simpl in *.
repeat break_match.
simpl in *.
assert (nwState h = (g, d0)) by eauto.
repeat find_rewrite.
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
-
unfold deghost in *.
simpl in *.
pose proof (RIR_handleMessage).
specialize (H5 (@mkPacket _ multi_params (pSrc p) (pDst p) (pBody p))).
eapply H5; eauto.
+
simpl in *.
repeat break_match.
simpl in *.
repeat find_rewrite.
eauto.
+
simpl in *.
unfold raft_refined_base_params, raft_refined_multi_params in *.
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
-
unfold deghost in *.
simpl in *.
eapply RIR_doLeader; eauto.
+
simpl in *.
repeat break_match.
simpl in *.
assert (nwState h = (g, d0)) by eauto.
repeat find_rewrite.
repeat find_inversion.
eauto.
+
simpl in *.
intros.
repeat break_match; simpl in *; repeat find_higher_order_rewrite; repeat break_match; congruence.
+
in_crush.
find_apply_hyp_hyp.
in_crush.
-
unfold deghost in *.
simpl in *.
eapply RIR_doGenericServer; eauto.
+
simpl in *.
repeat break_match.
simpl in *.
assert (nwState h = (g, d0)) by eauto.
repeat find_rewrite.
repeat find_inversion.
eauto.
+
simpl in *.
intros.
repeat break_match; simpl in *; repeat find_higher_order_rewrite; repeat break_match; congruence.
+
in_crush.
find_apply_hyp_hyp.
in_crush.
