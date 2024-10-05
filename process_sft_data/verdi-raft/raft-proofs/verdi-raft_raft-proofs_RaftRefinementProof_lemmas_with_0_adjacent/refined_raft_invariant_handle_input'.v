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

Lemma refined_raft_invariant_handle_input' P : forall h inp net st' ps' gd out d l, refined_raft_net_invariant_timeout' P -> refined_raft_net_invariant_client_request' P -> handleInput h inp (snd (nwState net h)) = (out, d, l) -> update_elections_data_input h inp (nwState net h) = gd -> P net -> refined_raft_intermediate_reachable net -> refined_raft_intermediate_reachable (mkNetwork ps' st') -> (forall h', st' h' = update name_eq_dec (nwState net) h (gd, d) h') -> (forall p', In p' ps' -> In p' (nwPackets net) \/ In p' (send_packets h l)) -> P (mkNetwork ps' st').
Proof using.
intros.
unfold handleInput, update_elections_data_input in *.
break_match; repeat break_let; repeat find_inversion; [eapply_prop refined_raft_net_invariant_timeout'| eapply_prop refined_raft_net_invariant_client_request']; eauto; subst; auto.
