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

Lemma candidates_vote_for_selves_l_invariant : forall (net : network), refined_raft_intermediate_reachable net -> candidates_vote_for_selves (deghost net).
Proof using cvfsi rri.
intros.
Admitted.

Lemma handleClientRequest_rvr : forall h net ps client id c out d l p t v, handleClientRequest h (snd (nwState net h)) client id c = (out, d, l) -> (forall p' : packet, In p' ps -> In p' (nwPackets net) \/ In p' (send_packets h l)) -> pBody p = RequestVoteReply t v -> In p ps -> In p (nwPackets net).
Proof using.
intros.
Admitted.

Lemma handleTimeout_rvr : forall h net ps out d l p t v, handleTimeout h (snd (nwState net h)) = (out, d, l) -> (forall p' : packet, In p' ps -> In p' (nwPackets net) \/ In p' (send_packets h l)) -> pBody p = RequestVoteReply t v -> In p ps -> In p (nwPackets net).
Proof using.
intros.
Admitted.

Lemma handleAppendEntries_rvr : forall h h' s ps ps' p d r tae li pli plt es lc t v, handleAppendEntries h s tae li pli plt es lc = (d, r) -> (forall p' : packet, In p' ps -> In p' ps' \/ p' = {| pSrc := h; pDst := h'; pBody := r |}) -> pBody p = RequestVoteReply t v -> In p ps -> In p ps'.
Proof using.
intros.
Admitted.

Lemma cronies_correct_client_request : refined_raft_net_invariant_client_request cronies_correct.
Proof using.
unfold refined_raft_net_invariant_client_request.
intros.
unfold cronies_correct in *; intuition.
-
unfold votes_received_cronies, handleClientRequest in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
unfold update_elections_data_client_request in *.
repeat break_match; find_inversion; subst; simpl in *; eauto; try congruence.
-
unfold cronies_votes in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
unfold update_elections_data_client_request in *.
repeat break_match; subst; simpl in *; eauto.
-
unfold votes_nw in *.
intros.
simpl in *.
assert (In p (nwPackets net)) by eauto using handleClientRequest_rvr.
repeat find_apply_hyp_hyp.
repeat find_higher_order_rewrite.
unfold update_elections_data_client_request in *.
repeat break_match; subst; repeat find_rewrite; simpl in *; intuition.
-
unfold votes_received_leaders in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
unfold handleClientRequest in *.
unfold update_elections_data_client_request in *.
Admitted.

Lemma cronies_correct_timeout : refined_raft_net_invariant_timeout cronies_correct.
Proof using.
unfold refined_raft_net_invariant_timeout.
intros.
unfold cronies_correct, update_elections_data_timeout in *; intuition.
-
unfold votes_received_cronies, handleTimeout, tryToBecomeLeader in *.
intros.
simpl in *.
repeat break_match; repeat find_inversion; subst; simpl in *; eauto; repeat find_higher_order_rewrite; repeat (break_if; simpl in *); auto; congruence.
-
unfold cronies_votes, handleTimeout, tryToBecomeLeader in *.
intros.
simpl in *.
repeat break_match; repeat find_inversion; subst; simpl in *; eauto; repeat find_higher_order_rewrite; repeat (break_if; simpl in *); auto; repeat find_inversion; subst; intuition; congruence.
-
unfold votes_nw in *.
intros.
simpl in *.
assert (In p (nwPackets net)) by eauto using handleTimeout_rvr.
repeat find_apply_hyp_hyp.
repeat find_higher_order_rewrite.
repeat break_match; subst; repeat find_rewrite; simpl in *; intuition.
-
unfold votes_received_leaders in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
unfold handleTimeout, tryToBecomeLeader in *.
simpl in *.
Admitted.

Lemma cronies_correct_append_entries : refined_raft_net_invariant_append_entries cronies_correct.
Proof using.
unfold refined_raft_net_invariant_append_entries.
intros.
unfold cronies_correct in *; intuition.
-
unfold votes_received_cronies, handleAppendEntries in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
unfold update_elections_data_appendEntries.
repeat break_match; repeat find_inversion; subst; simpl in *; eauto; repeat find_higher_order_rewrite; repeat (break_if; simpl in *); intuition; try congruence.
-
unfold cronies_votes in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
unfold update_elections_data_appendEntries in *.
repeat break_match; repeat find_inversion; subst; simpl in *; eauto.
-
unfold votes_nw in *.
intros.
simpl in *.
assert (In p0 (xs ++ ys)) by eauto using handleAppendEntries_rvr.
assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
repeat find_apply_hyp_hyp.
repeat find_higher_order_rewrite.
unfold update_elections_data_appendEntries in *.
repeat break_match; subst; repeat find_rewrite; simpl in *; intuition.
-
unfold votes_received_leaders in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
repeat break_if; eauto.
subst.
simpl in *.
unfold handleAppendEntries in *.
Admitted.

Lemma cronies_correct_append_entries_reply : refined_raft_net_invariant_append_entries_reply cronies_correct.
Proof using.
unfold refined_raft_net_invariant_append_entries_reply.
intros.
unfold cronies_correct in *; intuition.
-
unfold votes_received_cronies, handleAppendEntriesReply, advanceCurrentTerm in *.
intros.
simpl in *.
repeat break_match; repeat find_inversion; subst; simpl in *; eauto; repeat find_higher_order_rewrite; repeat (break_if; simpl in *); intuition; try congruence.
-
unfold cronies_votes in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
repeat break_match; subst; simpl in *; eauto.
-
unfold votes_nw in *.
intros.
simpl in *.
assert (In p0 (xs ++ ys)) by eauto using handleAppendEntriesReply_rvr.
assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
repeat find_apply_hyp_hyp.
repeat find_higher_order_rewrite.
repeat break_match; subst; repeat find_rewrite; simpl in *; intuition.
-
unfold votes_received_leaders in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
repeat break_if; eauto.
subst.
simpl in *.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma handleRequestVote_true_votedFor : forall h st t src lli llt d t', handleRequestVote h st t src lli llt = (d, RequestVoteReply t' true) -> currentTerm d = t' /\ votedFor d = Some src.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Lemma update_elections_data_requestVote_cronies : forall h h' t h'' lli llt st, cronies (update_elections_data_requestVote h h' t h'' lli llt st) = cronies (fst st).
Proof using.
intros.
unfold update_elections_data_requestVote in *.
Admitted.

Lemma handleRequestVote_votesReceived : forall h st t h' lli llt st' m, handleRequestVote h st t h' lli llt = (st', m) -> votesReceived st' = votesReceived st.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Lemma handleRequestVote_currentTerm_same_or_follower : forall h st t h' lli llt st' m, handleRequestVote h st t h' lli llt = (st', m) -> (currentTerm st' = currentTerm st /\ type st' = type st) \/ type st' = Follower.
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Lemma update_elections_data_requestVote_votes_preserved : forall t c h h' t' h'' lli llt st, In (t, c) (votes (fst st)) -> In (t, c) (votes (update_elections_data_requestVote h h' t' h'' lli llt st)).
Proof using.
intros.
unfold update_elections_data_requestVote.
Admitted.

Lemma update_elections_data_requestVote_votedFor : forall h h' t lli llt st st' m, handleRequestVote h (snd st) t h' lli llt = (st', m) -> votedFor st' = Some h' -> In (currentTerm st', h') (votes (update_elections_data_requestVote h h' t h' lli llt st)) \/ (votedFor st' = votedFor (snd st) /\ currentTerm st' = currentTerm (snd st)).
Proof using.
intros.
unfold update_elections_data_requestVote in *.
Admitted.

Lemma handleAppendEntriesReply_rvr : forall h s src ps ps' p d l tae es res t v, handleAppendEntriesReply h s src tae es res = (d, l) -> (forall p' : packet, In p' ps -> In p' ps' \/ In p' (send_packets h l)) -> pBody p = RequestVoteReply t v -> In p ps -> In p ps'.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *; repeat break_match; repeat find_inversion; subst; simpl in *; find_apply_hyp_hyp; in_crush; congruence.
