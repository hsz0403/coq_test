Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AppendEntriesRequestsCameFromLeadersInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.OneLeaderPerTermInterface.
Require Import VerdiRaft.AppendEntriesLeaderInterface.
Section AppendEntriesLeader.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {aecfli : append_entries_came_from_leaders_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Context {olpti : one_leader_per_term_interface}.
Definition type_term_log_monotonic st st' := type st' = Leader -> type st = Leader /\ currentTerm st' = currentTerm st /\ (forall e, In e (log st) -> In e (log st')).
Notation appendEntries_leader_predicate ps st := (forall p t lid pli plt es lci e, In p ps -> pBody p = AppendEntries t lid pli plt es lci -> In e es -> currentTerm st = t -> type st = Leader -> In e (log st)).
Instance appendeli : append_entries_leader_interface.
Proof.
split.
exact appendEntries_leader_invariant.
End AppendEntriesLeader.

Lemma appendEntries_leader_init : refined_raft_net_invariant_init appendEntries_leader.
Proof using.
unfold refined_raft_net_invariant_init, appendEntries_leader.
simpl.
Admitted.

Lemma appendEntries_leader_predicate_TTLM_preserved : forall ps st st', appendEntries_leader_predicate ps st -> type_term_log_monotonic st st' -> appendEntries_leader_predicate ps st'.
Proof using.
unfold type_term_log_monotonic.
intuition.
repeat find_rewrite.
Admitted.

Lemma handleClientRequest_TTLM : forall h st client id c out st' l, handleClientRequest h st client id c = (out, st', l) -> type_term_log_monotonic st st'.
Proof using.
unfold type_term_log_monotonic.
intros.
find_copy_apply_lem_hyp handleClientRequest_type.
find_copy_apply_lem_hyp handleClientRequest_log.
intuition; try congruence.
break_exists.
intuition.
subst.
repeat find_rewrite.
Admitted.

Lemma appendEntries_leader_client_request : refined_raft_net_invariant_client_request appendEntries_leader.
Proof using.
unfold refined_raft_net_invariant_client_request, appendEntries_leader.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
-
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
eapply appendEntries_leader_predicate_TTLM_preserved; eauto using handleClientRequest_TTLM.
eauto.
+
eauto.
-
find_apply_lem_hyp handleClientRequest_packets.
subst.
simpl in *.
Admitted.

Lemma handleTimeout_TTLM : forall h st out st' l, handleTimeout h st = (out, st', l) -> type_term_log_monotonic st st'.
Proof using.
unfold type_term_log_monotonic.
intros.
find_copy_apply_lem_hyp handleTimeout_type.
find_apply_lem_hyp handleTimeout_log_same.
Admitted.

Lemma handleAppendEntries_TTLM : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> type_term_log_monotonic st st'.
Proof using.
unfold type_term_log_monotonic, handleAppendEntries.
intros.
Admitted.

Lemma appendEntries_leader_append_entries : refined_raft_net_invariant_append_entries appendEntries_leader.
Proof using.
unfold refined_raft_net_invariant_append_entries, appendEntries_leader.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
-
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
eapply appendEntries_leader_predicate_TTLM_preserved; eauto using handleAppendEntries_TTLM.
eauto.
+
eauto.
-
find_apply_lem_hyp handleAppendEntries_not_append_entries.
subst.
exfalso.
Admitted.

Lemma handleAppendEntriesReply_TTLM : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> type_term_log_monotonic st st'.
Proof using.
unfold type_term_log_monotonic, handleAppendEntriesReply, advanceCurrentTerm.
intros.
Admitted.

Lemma appendEntries_leader_append_entries_reply : refined_raft_net_invariant_append_entries_reply appendEntries_leader.
Proof using.
unfold refined_raft_net_invariant_append_entries_reply, appendEntries_leader.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
-
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
eapply appendEntries_leader_predicate_TTLM_preserved; eauto using handleAppendEntriesReply_TTLM.
eauto.
+
eauto.
-
find_apply_lem_hyp handleAppendEntriesReply_packets.
subst.
simpl in *.
Admitted.

Lemma handleRequestVote_TTLM : forall st h h' t lli llt st' m, handleRequestVote h st t h' lli llt = (st', m) -> type_term_log_monotonic st st'.
Proof using.
unfold type_term_log_monotonic, handleRequestVote, advanceCurrentTerm.
intros.
Admitted.

Lemma appendEntries_leader_request_vote : refined_raft_net_invariant_request_vote appendEntries_leader.
Proof using.
unfold refined_raft_net_invariant_request_vote, appendEntries_leader.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
-
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
eapply appendEntries_leader_predicate_TTLM_preserved; eauto using handleRequestVote_TTLM.
eauto.
+
eauto.
-
find_apply_lem_hyp handleRequestVote_no_append_entries.
subst.
exfalso.
Admitted.

Lemma handleRequestVoteReply_spec' : forall h st h' t r st', handleRequestVoteReply h st h' t r = st' -> type st' = Follower \/ st' = st \/ type st' = Candidate \/ (type st' = Leader /\ type st = Candidate /\ log st' = log st /\ r = true /\ t = currentTerm st /\ wonElection (dedup name_eq_dec (h' :: votesReceived st)) = true /\ currentTerm st' = currentTerm st).
Proof using.
unfold handleRequestVoteReply.
intros.
Admitted.

Lemma update_elections_data_RVR_ascending_leaderLog : forall h src t1 v st, type (snd st) = Candidate -> type (handleRequestVoteReply h (snd st) src t1 v) = Leader -> exists ll, In (currentTerm (snd st), ll) (leaderLogs (update_elections_data_requestVoteReply h src t1 v st)).
Proof using.
unfold update_elections_data_requestVoteReply, handleRequestVoteReply.
intros.
repeat find_rewrite.
simpl in *.
Admitted.

Lemma appendEntries_leader_request_vote_reply : refined_raft_net_invariant_request_vote_reply' appendEntries_leader.
Proof using lltsi ollpti aecfli.
unfold refined_raft_net_invariant_request_vote_reply', appendEntries_leader.
simpl.
intros.
find_apply_hyp_hyp.
find_copy_apply_lem_hyp handleRequestVoteReply_spec'.
repeat find_higher_order_rewrite.
update_destruct_simplify.
-
rewrite handleRequestVoteReply_same_log.
intuition; try congruence.
+
repeat find_rewrite.
eauto using in_middle_insert with *.
+
subst.
match goal with | [ H : pBody _ = AppendEntries _ _ _ _ _ _ |- _ ] => copy_eapply (append_entries_came_from_leaders_invariant net) H end; eauto.
break_exists.
assert (pDst p = pSrc p0).
{
destruct (name_eq_dec (pDst p) (pSrc p0)); auto.
find_copy_apply_lem_hyp update_elections_data_RVR_ascending_leaderLog; auto.
break_exists.
repeat find_rewrite.
match goal with | [ H : refined_raft_intermediate_reachable ?the_net, H': In (?the_t, ?the_ll) (leaderLogs (update_elections_data_requestVoteReply _ _ _ _ _)), H'' : In (_, ?the_ll') (leaderLogs (fst _)) |- _ ] => match the_net with | context [ st' ] => apply one_leaderLog_per_term_host_invariant with (net0 := the_net) (t := the_t) (ll := the_ll) (ll' := the_ll') end end; auto; simpl; repeat find_higher_order_rewrite; rewrite_update; simpl; auto.
}
exfalso.
repeat find_rewrite.
eapply lt_irrefl.
eapply leaderLogs_currentTerm_sanity_candidate_invariant; [|eauto|]; auto.
-
Admitted.

Lemma doLeader_TTLM : forall st h os st' ms, doLeader st h = (os, st', ms) -> type_term_log_monotonic st st'.
Proof using.
unfold doLeader, type_term_log_monotonic.
intros.
Admitted.

Lemma appendEntries_leader_timeout : refined_raft_net_invariant_timeout appendEntries_leader.
Proof using.
unfold refined_raft_net_invariant_timeout, appendEntries_leader.
simpl.
intros.
find_apply_hyp_hyp.
intuition.
-
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
eapply appendEntries_leader_predicate_TTLM_preserved; eauto using handleTimeout_TTLM.
eauto.
+
eauto.
-
do_in_map.
find_eapply_lem_hyp handleTimeout_packets; eauto.
subst.
exfalso.
eauto 10.
