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

Lemma msg_refined_raft_invariant_handle_message P : forall xs p ys net st' ps' gd d l, msg_refined_raft_net_invariant_append_entries P -> msg_refined_raft_net_invariant_append_entries_reply P -> msg_refined_raft_net_invariant_request_vote P -> msg_refined_raft_net_invariant_request_vote_reply P -> handleMessage (pSrc p) (pDst p) (snd (pBody p)) (snd (nwState net (pDst p))) = (d, l) -> update_elections_data_net (pDst p) (pSrc p) (snd (pBody p)) (nwState net (pDst p)) = gd -> P net -> msg_refined_raft_intermediate_reachable net -> nwPackets net = xs ++ p :: ys -> (forall h, st' h = update name_eq_dec (nwState net) (pDst p) (gd, d) h) -> (forall p', In p' ps' -> In p' (xs ++ ys) \/ In p' (send_packets (pDst p) (@add_ghost_msg _ _ ghost_log_params (pDst p) (gd, d) l))) -> P (mkNetwork ps' st').
Proof using.
intros.
unfold handleMessage, update_elections_data_net in *.
break_match; repeat break_let; repeat find_inversion; [eapply_prop msg_refined_raft_net_invariant_request_vote| eapply_prop msg_refined_raft_net_invariant_request_vote_reply| eapply_prop msg_refined_raft_net_invariant_append_entries| eapply_prop msg_refined_raft_net_invariant_append_entries_reply]; eauto; unfold send_packets in *; simpl in *; intros; subst; auto; find_apply_hyp_hyp; intuition.
