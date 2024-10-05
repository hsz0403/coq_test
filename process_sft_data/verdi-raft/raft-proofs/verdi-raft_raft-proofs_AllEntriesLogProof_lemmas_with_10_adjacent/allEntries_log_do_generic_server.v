Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.AllEntriesLeaderLogsTermInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.AllEntriesTermSanityInterface.
Require Import VerdiRaft.AllEntriesLogInterface.
Section AllEntriesLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {llli : logs_leaderLogs_interface}.
Context {aerlli : append_entries_leaderLogs_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {aellti : allEntries_leaderLogs_term_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {tsi : term_sanity_interface}.
Context {rri : raft_refinement_interface}.
Context {aetsi : allEntries_term_sanity_interface}.
Definition no_entries_past_current_term_host_lifted net := forall (h : name) e, In e (log (snd (nwState net h))) -> eTerm e <= currentTerm (snd (nwState net h)).
Ltac inList x ls := match ls with | x => idtac | (_, x) => idtac | (?LS, _) => inList x LS end.
Ltac app f ls := match ls with | (?LS, ?X) => f X || app f LS || fail 1 | _ => f ls end.
Ltac all f ls := match ls with | (?LS, ?X) => f X; all f LS | (_, _) => fail 1 | _ => f ls end.
Instance aeli : allEntries_log_interface.
split.
eauto using allEntries_log_invariant.
Defined.
End AllEntriesLog.

Lemma handleRequestVoteReply_log' : forall h st h' t r, log (handleRequestVoteReply h st h' t r) = log st.
Proof using.
Admitted.

Lemma allEntries_log_request_vote_reply : refined_raft_net_invariant_request_vote_reply allEntries_log.
Proof using.
red.
unfold allEntries_log in *.
intros.
simpl in *.
find_copy_apply_lem_hyp handleRequestVoteReply_currentTerm_leaderId.
repeat find_higher_order_rewrite.
Admitted.

Lemma update_elections_data_client_request_allEntries' : forall h st client id c out st' ms t e, handleClientRequest h (snd st) client id c = (out, st', ms) -> In (t, e) (allEntries (update_elections_data_client_request h st client id c)) -> In (t, e) (allEntries (fst st)) \/ In e (log st').
Proof using.
intros.
unfold update_elections_data_client_request in *.
repeat break_match; repeat find_inversion; auto.
simpl in *.
intuition.
find_inversion.
repeat find_rewrite.
Admitted.

Lemma handleClientRequest_currentTerm_leaderId : forall h st client id c out st' ms, handleClientRequest h st client id c = (out, st', ms) -> currentTerm st' = currentTerm st /\ leaderId st' = leaderId st.
Proof using.
intros.
unfold handleClientRequest in *.
subst.
Admitted.

Lemma allEntries_log_client_request : refined_raft_net_invariant_client_request allEntries_log.
Proof using.
red.
unfold allEntries_log in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
Admitted.

Lemma handleTimeout_currentTerm_leaderId : forall h st out st' ms, handleTimeout h st = (out, st', ms) -> currentTerm st < currentTerm st' \/ currentTerm st' = currentTerm st /\ leaderId st' = leaderId st.
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
subst.
Admitted.

Lemma allEntries_log_timeout : refined_raft_net_invariant_timeout allEntries_log.
Proof using.
red.
unfold allEntries_log in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
Admitted.

Lemma doLeader_currentTerm_leaderId : forall st h out st' m, doLeader st h = (out, st', m) -> currentTerm st' = currentTerm st /\ leaderId st' = leaderId st.
Proof using.
intros.
unfold doLeader, advanceCommitIndex in *.
Admitted.

Lemma allEntries_log_do_leader : refined_raft_net_invariant_do_leader allEntries_log.
Proof using.
red.
unfold allEntries_log in *.
intros.
simpl in *.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
repeat find_higher_order_rewrite.
find_copy_apply_lem_hyp doLeader_log.
find_apply_lem_hyp doLeader_currentTerm_leaderId.
Admitted.

Lemma doGenericServer_currentTerm_leaderId : forall st h out st' m, doGenericServer h st = (out, st', m) -> currentTerm st' = currentTerm st /\ leaderId st' = leaderId st.
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Lemma allEntries_log_init : refined_raft_net_invariant_init allEntries_log.
Proof using.
red.
unfold allEntries_log.
intros.
simpl in *.
Admitted.

Lemma allEntries_log_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset allEntries_log.
Proof using.
red.
unfold allEntries_log in *.
intros.
repeat find_reverse_higher_order_rewrite.
find_apply_hyp_hyp.
intuition.
right.
break_exists_exists.
repeat find_higher_order_rewrite.
Admitted.

Lemma allEntries_log_reboot : refined_raft_net_invariant_reboot allEntries_log.
Proof using.
red.
unfold allEntries_log in *.
intros.
simpl in *.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
repeat find_higher_order_rewrite.
subst.
unfold reboot in *.
Admitted.

Lemma allEntries_log_invariant : forall net, refined_raft_intermediate_reachable net -> allEntries_log net.
Proof using aetsi rri tsi llsi ollpti llci aellti rlmli aerlli llli.
intros.
apply refined_raft_net_invariant; auto.
-
exact allEntries_log_init.
-
exact allEntries_log_client_request.
-
exact allEntries_log_timeout.
-
exact allEntries_log_append_entries.
-
exact allEntries_log_append_entries_reply.
-
exact allEntries_log_request_vote.
-
exact allEntries_log_request_vote_reply.
-
exact allEntries_log_do_leader.
-
exact allEntries_log_do_generic_server.
-
exact allEntries_log_state_same_packet_subset.
-
Admitted.

Instance aeli : allEntries_log_interface.
split.
Admitted.

Lemma allEntries_log_do_generic_server : refined_raft_net_invariant_do_generic_server allEntries_log.
Proof using.
red.
unfold allEntries_log in *.
intros.
simpl in *.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
repeat find_higher_order_rewrite.
find_copy_apply_lem_hyp doGenericServer_log.
find_apply_lem_hyp doGenericServer_currentTerm_leaderId.
destruct_update; simpl in *; eauto; find_apply_hyp_hyp; repeat find_rewrite; intuition; right; break_exists_exists; intuition; find_higher_order_rewrite; destruct_update; simpl in *; auto.
