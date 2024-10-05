Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.LeaderLogsLogMatchingInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LeaderLogsLogPropertiesInterface.
Section LogsLeaderLogs.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {lllmi : leaderLogs_entries_match_interface}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {nisi : nextIndex_safety_interface}.
Context {si : sorted_interface}.
Context {lpholli : log_properties_hold_on_leader_logs_interface}.
Definition weak_sanity pli ll ll' := pli = 0 -> (exists e, eIndex e = 0 /\ In e ll) \/ ll = ll'.
Definition logs_leaderLogs_nw_weak net := forall p t n pli plt es ci e, In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> In e es -> exists leader ll es' ll', In (eTerm e, ll) (leaderLogs (fst (nwState net leader))) /\ Prefix ll' ll /\ removeAfterIndex es (eIndex e) = es' ++ ll' /\ (forall e', In e' es' -> eTerm e' = eTerm e) /\ weak_sanity pli ll ll'.
Definition logs_leaderLogs_inductive net := logs_leaderLogs net /\ logs_leaderLogs_nw net.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Instance llli : logs_leaderLogs_interface.
Proof.
split; eauto using logs_leaderLogs_invariant, logs_leaderLogs_nw_invariant.
End LogsLeaderLogs.

Theorem lift_sorted : forall net, refined_raft_intermediate_reachable net -> logs_sorted (deghost net).
Proof using si rri.
intros.
Admitted.

Theorem lift_logs_sorted : forall net h, refined_raft_intermediate_reachable net -> sorted (log (snd (nwState net h))).
Proof using si rri.
intros.
find_apply_lem_hyp lift_sorted.
unfold logs_sorted, logs_sorted_host in *.
intuition.
unfold deghost in *.
simpl in *.
Admitted.

Lemma lift_nextIndex_safety : forall net, refined_raft_intermediate_reachable net -> nextIndex_safety (deghost net).
Proof using nisi rri.
intros.
Admitted.

Lemma nextIndex_sanity : forall net h h', refined_raft_intermediate_reachable net -> type (snd (nwState net h)) = Leader -> pred (getNextIndex (snd (nwState net h)) h') <> 0 -> exists e, findAtIndex (log (snd (nwState net h))) (pred (getNextIndex (snd (nwState net h)) h')) = Some e.
Proof using si nisi rlmli rri.
intros.
find_copy_apply_lem_hyp entries_contiguous_invariant.
find_copy_apply_lem_hyp lift_nextIndex_safety.
assert (pred (getNextIndex (snd (nwState net h)) h') > 0) by omega.
unfold nextIndex_safety in *.
match goal with | H : forall _ _, type _ = _ -> _ |- _ => specialize (H h h') end.
intuition.
unfold entries_contiguous in *.
specialize (H2 h).
unfold contiguous_range_exact_lo in *.
intuition.
match goal with | H : forall _, _ < _ <= _ -> _ |- _ => specialize (H (pred (getNextIndex (snd (nwState net h)) h'))) end.
unfold raft_refined_base_params in *.
repeat find_rewrite_lem deghost_spec.
intuition.
break_exists_exists.
intuition.
Admitted.

Lemma update_elections_data_client_request_leaderLogs : forall h st client id c, leaderLogs (update_elections_data_client_request h st client id c) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_client_request in *.
intros.
Admitted.

Lemma update_elections_data_timeout_leaderLogs : forall h st, leaderLogs (update_elections_data_timeout h st) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_timeout.
intros.
Admitted.

Lemma update_elections_data_appendEntries_leaderLogs : forall h st t h' pli plt es ci, leaderLogs (update_elections_data_appendEntries h st t h' pli plt es ci) = leaderLogs (fst st).
Proof using.
intros.
unfold update_elections_data_appendEntries.
Admitted.

Lemma update_elections_data_requestVote_leaderLogs : forall h h' t lli llt st, leaderLogs (update_elections_data_requestVote h h' t h' lli llt st) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_requestVote.
intros.
Admitted.

Lemma update_elections_data_requestVoteReply_leaderLogs : forall h h' t st t' ll' r, In (t', ll') (leaderLogs (fst st)) -> In (t', ll') (leaderLogs (update_elections_data_requestVoteReply h h' t r st)).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
repeat break_match; auto.
simpl in *.
Admitted.

Lemma contiguous_log_property : log_property (fun l => contiguous_range_exact_lo l 0).
Proof using rlmli.
red.
intros.
Admitted.

Lemma logs_leaderLogs_nw_weaken : forall net, logs_leaderLogs_nw net -> logs_leaderLogs_nw_weak net.
Proof using.
intros.
unfold logs_leaderLogs_nw, logs_leaderLogs_nw_weak, weak_sanity in *.
intros.
eapply_prop_hyp In In; eauto.
break_exists_exists; intuition; subst; try omega.
break_exists; intuition; eauto.
