Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RefinementCommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeaderLogsVotesWithLogInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.VotesVotesWithLogCorrespondInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Section OneLeaderLogPerTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {llvwli : leaderLogs_votesWithLog_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Context {vvci : votes_votesWithLog_correspond_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Ltac start := red; unfold one_leaderLog_per_term; simpl; intros.
Ltac start_update := start; repeat find_higher_order_rewrite; repeat (update_destruct; subst; rewrite_update); [| | |eauto].
Ltac start_unchanged := red; intros; eapply one_leaderLog_per_term_unchanged; eauto; subst.
Ltac unchanged lem := start_unchanged; apply lem.
Instance ollpti : one_leaderLog_per_term_interface.
Proof.
split; intros; intro_refined_invariant one_leaderLog_per_term_invariant; red; eapply_prop one_leaderLog_per_term.
End OneLeaderLogPerTerm.

Lemma one_leaderLog_per_term_invariant : forall net, refined_raft_intermediate_reachable net -> one_leaderLog_per_term net.
Proof using lltsi vvci cci vci llvwli rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply one_leaderLog_per_term_init.
-
apply one_leaderLog_per_term_client_request.
-
apply one_leaderLog_per_term_timeout.
-
apply one_leaderLog_per_term_append_entries.
-
apply one_leaderLog_per_term_append_entries_reply.
-
apply one_leaderLog_per_term_request_vote.
-
apply one_leaderLog_per_term_request_vote_reply.
-
apply one_leaderLog_per_term_do_leader.
-
apply one_leaderLog_per_term_do_generic_server.
-
apply one_leaderLog_per_term_state_same_packet_subset.
-
apply one_leaderLog_per_term_reboot.
