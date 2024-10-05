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
eauto.
