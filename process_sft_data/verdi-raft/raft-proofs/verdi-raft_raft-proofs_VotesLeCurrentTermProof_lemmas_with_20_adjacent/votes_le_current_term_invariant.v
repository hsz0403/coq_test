Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.VotesLeCurrentTermInterface.
Set Bullet Behavior "Strict Subproofs".
Section VotesLeCurrentTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Ltac start_proof := cbn [nwState]; intros; subst; repeat find_higher_order_rewrite; update_destruct; rewrite_update; cbn [fst snd] in *; eauto.
Instance vlcti : votes_le_current_term_interface.
Proof.
split.
auto using votes_le_current_term_invariant.
End VotesLeCurrentTerm.

Lemma votes_le_current_term_client_request : refined_raft_net_invariant_client_request votes_le_currentTerm.
Proof using.
unfold refined_raft_net_invariant_client_request, votes_le_currentTerm.
start_proof.
erewrite handleClientRequest_currentTerm by eauto.
rewrite @votes_update_elections_data_client_request in *.
Admitted.

Lemma votes_le_current_term_timeout : refined_raft_net_invariant_timeout votes_le_currentTerm.
Proof using.
unfold refined_raft_net_invariant_timeout, votes_le_currentTerm.
start_proof.
find_copy_eapply_lem_hyp votes_update_elections_data_timeout; eauto.
break_or_hyp; auto with *.
find_apply_lem_hyp handleTimeout_currentTerm.
find_apply_hyp_hyp.
Admitted.

Lemma votes_le_current_term_append_entries : refined_raft_net_invariant_append_entries votes_le_currentTerm.
Proof using.
unfold refined_raft_net_invariant_append_entries, votes_le_currentTerm.
start_proof.
rewrite @votes_same_append_entries in *.
find_apply_lem_hyp handleAppendEntries_currentTerm.
find_apply_hyp_hyp.
Admitted.

Lemma votes_le_current_term_append_entries_reply : refined_raft_net_invariant_append_entries_reply votes_le_currentTerm.
Proof using.
unfold refined_raft_net_invariant_append_entries_reply, votes_le_currentTerm.
start_proof.
find_apply_lem_hyp handleAppendEntriesReply_currentTerm.
find_apply_hyp_hyp.
Admitted.

Lemma votes_le_current_term_request_vote : refined_raft_net_invariant_request_vote votes_le_currentTerm.
Proof using.
unfold refined_raft_net_invariant_request_vote, votes_le_currentTerm.
start_proof.
find_eapply_lem_hyp votes_update_elections_data_request_vote; eauto.
intuition.
find_apply_hyp_hyp.
Admitted.

Lemma votes_le_current_term_request_vote_reply : refined_raft_net_invariant_request_vote_reply votes_le_currentTerm.
Proof using.
unfold refined_raft_net_invariant_request_vote_reply, votes_le_currentTerm.
start_proof.
find_eapply_lem_hyp votes_update_elections_data_request_vote_reply; eauto.
Admitted.

Lemma votes_le_current_term_do_leader : refined_raft_net_invariant_do_leader votes_le_currentTerm.
Proof using.
unfold refined_raft_net_invariant_do_leader, votes_le_currentTerm.
start_proof.
assert (gd = (fst (nwState net h)) /\ d = snd (nwState net h)) by (repeat find_rewrite; auto).
break_and.
subst.
erewrite doLeader_currentTerm by eauto.
Admitted.

Lemma votes_le_current_term_do_generic_server : refined_raft_net_invariant_do_generic_server votes_le_currentTerm.
Proof using.
unfold refined_raft_net_invariant_do_generic_server, votes_le_currentTerm.
start_proof.
assert (gd = (fst (nwState net h)) /\ d = snd (nwState net h)) by (repeat find_rewrite; auto).
break_and.
subst.
erewrite doGenericServer_currentTerm by eauto.
Admitted.

Lemma votes_le_current_term_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset votes_le_currentTerm.
Proof using.
unfold refined_raft_net_invariant_state_same_packet_subset, votes_le_currentTerm.
intros.
repeat find_reverse_higher_order_rewrite.
Admitted.

Lemma votes_le_current_term_reboot : refined_raft_net_invariant_reboot votes_le_currentTerm.
Proof using.
unfold refined_raft_net_invariant_reboot, votes_le_currentTerm.
start_proof.
unfold reboot.
simpl.
assert (gd = (fst (nwState net h)) /\ d = snd (nwState net h)) by (repeat find_rewrite; auto).
break_and.
subst.
Admitted.

Theorem votes_le_current_term_init : refined_raft_net_invariant_init votes_le_currentTerm.
Proof using.
unfold refined_raft_net_invariant_init, votes_le_currentTerm.
simpl.
Admitted.

Instance vlcti : votes_le_current_term_interface.
Proof.
split.
Admitted.

Theorem votes_le_current_term_invariant : forall net, refined_raft_intermediate_reachable net -> votes_le_currentTerm net.
Proof using rri.
intros.
eapply refined_raft_net_invariant; eauto.
-
apply votes_le_current_term_init.
-
apply votes_le_current_term_client_request.
-
apply votes_le_current_term_timeout.
-
apply votes_le_current_term_append_entries.
-
apply votes_le_current_term_append_entries_reply.
-
apply votes_le_current_term_request_vote.
-
apply votes_le_current_term_request_vote_reply.
-
apply votes_le_current_term_do_leader.
-
apply votes_le_current_term_do_generic_server.
-
apply votes_le_current_term_state_same_packet_subset.
-
apply votes_le_current_term_reboot.
