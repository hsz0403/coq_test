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
eauto.
