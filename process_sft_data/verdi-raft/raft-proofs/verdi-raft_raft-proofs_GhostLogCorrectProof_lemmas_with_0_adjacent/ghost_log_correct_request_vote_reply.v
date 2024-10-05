Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RaftMsgRefinementInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.GhostLogCorrectInterface.
Section GhostLogCorrectProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rmri : raft_msg_refinement_interface}.
Context {nisi : nextIndex_safety_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Definition lifted_nextIndex_safety net : Prop := forall h h', type (snd (nwState net h)) = Leader -> pred (getNextIndex (snd (nwState net h)) h') <= maxIndex (log (snd (nwState net h))).
Definition lifted_entries_contiguous net := forall h, contiguous_range_exact_lo (log (snd (nwState net h))) 0.
Definition lifted_entries_sorted net := forall h, sorted (log (snd (nwState net h))).
Instance glci : ghost_log_correct_interface.
Proof.
split.
intros.
apply msg_refined_raft_net_invariant; auto.
-
apply ghost_log_correct_init.
-
apply ghost_log_correct_client_request.
-
apply ghost_log_correct_timeout.
-
apply ghost_log_correct_append_entries.
-
apply ghost_log_correct_append_entries_reply.
-
apply ghost_log_correct_request_vote.
-
apply ghost_log_correct_request_vote_reply.
-
apply ghost_log_correct_do_leader.
-
apply ghost_log_correct_do_generic_server.
-
apply ghost_log_correct_state_same_packet_subset.
-
apply ghost_log_correct_reboot.
End GhostLogCorrectProof.

Lemma ghost_log_correct_request_vote_reply : msg_refined_raft_net_invariant_request_vote_reply ghost_log_correct.
Proof using.
red.
unfold ghost_log_correct.
intros.
simpl in *.
find_apply_hyp_hyp; intuition; eauto.
