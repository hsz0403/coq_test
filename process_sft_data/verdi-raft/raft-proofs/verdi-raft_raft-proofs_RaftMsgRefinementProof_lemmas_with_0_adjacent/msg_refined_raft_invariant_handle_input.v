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

Lemma msg_refined_raft_invariant_handle_input P : forall h inp net st' ps' gd out d l, msg_refined_raft_net_invariant_timeout P -> msg_refined_raft_net_invariant_client_request P -> handleInput h inp (snd (nwState net h)) = (out, d, l) -> update_elections_data_input h inp (nwState net h) = gd -> P net -> msg_refined_raft_intermediate_reachable net -> (forall h', st' h' = update name_eq_dec (nwState net) h (gd, d) h') -> (forall p', In p' ps' -> In p' (nwPackets net) \/ In p' (send_packets h (@add_ghost_msg _ _ ghost_log_params h (gd, d) l))) -> P (mkNetwork ps' st').
Proof using.
intros.
unfold handleInput, update_elections_data_input in *.
break_match; repeat break_let; repeat find_inversion; [eapply_prop msg_refined_raft_net_invariant_timeout| eapply_prop msg_refined_raft_net_invariant_client_request]; eauto; subst; auto.
