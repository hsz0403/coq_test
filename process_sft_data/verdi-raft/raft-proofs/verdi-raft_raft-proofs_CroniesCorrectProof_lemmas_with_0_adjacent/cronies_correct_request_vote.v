Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CandidatesVoteForSelvesInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Section CroniesCorrectProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {vci : votes_correct_interface}.
Context {cvfsi : candidates_vote_for_selves_interface}.
Instance cci : cronies_correct_interface.
Proof.
split.
auto using cronies_correct_invariant.
End CroniesCorrectProof.

Lemma cronies_correct_request_vote : refined_raft_net_invariant_request_vote cronies_correct.
Proof using vci.
unfold refined_raft_net_invariant_request_vote.
intros.
unfold cronies_correct in *; intuition.
-
unfold votes_received_cronies in *.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
break_if; simpl in *; subst; eauto.
rewrite update_elections_data_requestVote_cronies.
find_copy_apply_lem_hyp handleRequestVote_votesReceived.
repeat find_rewrite.
find_apply_lem_hyp handleRequestVote_currentTerm_same_or_follower.
match goal with | H : currentTerm _ = currentTerm _ /\ _ \/ _ |- _ => destruct H end; try break_and; repeat find_rewrite; eauto.
intuition; congruence.
-
unfold cronies_votes in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
repeat break_if; subst; simpl in *; eauto; try rewrite update_elections_data_requestVote_cronies in *; eauto using update_elections_data_requestVote_votes_preserved.
-
unfold votes_nw in *.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
find_apply_hyp_hyp.
intuition.
+
assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
simpl.
break_if; simpl in *; eauto.
eapply update_elections_data_requestVote_votes_preserved.
repeat find_reverse_rewrite.
eauto.
+
unfold raft_data in *.
repeat find_rewrite.
repeat find_inversion.
repeat (subst; simpl in *).
find_copy_apply_lem_hyp handleRequestVote_true_votedFor.
intuition.
repeat find_rewrite.
simpl in *.
break_if; simpl in *; try congruence.
subst.
find_apply_lem_hyp update_elections_data_requestVote_votedFor; intuition.
repeat find_rewrite.
apply update_elections_data_requestVote_votes_preserved.
eapply votes_correct_invariant; eauto.
-
unfold votes_received_leaders in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
repeat break_if; eauto.
subst.
simpl in *.
find_copy_apply_lem_hyp handleRequestVote_votesReceived.
find_apply_lem_hyp handleRequestVote_currentTerm_same_or_follower.
intuition; repeat find_rewrite; try congruence; eauto.
