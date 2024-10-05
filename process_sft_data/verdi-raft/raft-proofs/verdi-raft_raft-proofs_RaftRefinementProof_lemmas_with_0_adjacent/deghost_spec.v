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

Lemma deghost_spec : forall (net : @network _ raft_refined_multi_params) h, nwState (deghost net) h = snd (nwState net h).
Proof using.
intros.
destruct net; auto.
