Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.EveryEntryWasCreatedInterface.
Require Import VerdiRaft.LeaderLogsCandidateEntriesInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.LeaderLogsSublogInterface.
Section LeaderLogsSublog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {lsi : leader_sublog_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Context {eewci : every_entry_was_created_interface}.
Context {llcei : leaderLogs_candidate_entries_interface}.
Context {cci : cronies_correct_interface}.
Context {vci : votes_correct_interface}.
Ltac start := repeat match goal with | [ H : _ |- _ ] => rewrite update_fun_comm with (f := fst) in H | [ H : _ |- _ ] => rewrite update_fun_comm with (f := snd) in H | [ H : _ |- _ ] => rewrite update_fun_comm with (f := leaderLogs) in H end; rewrite update_fun_comm with (f := snd); simpl in *; match goal with | [ H : context [ type ] |- _ ] => rewrite update_fun_comm in H; rewrite update_nop_ext' in H by auto end; match goal with | [ H : context [ currentTerm ] |- _ ] => rewrite update_fun_comm in H; rewrite update_nop_ext' in H by auto end.
Arguments dedup : simpl never.
Instance llsli : leaderLogs_sublog_interface.
Proof.
split.
exact leaderLogs_sublog_invariant.
End LeaderLogsSublog.

Theorem leaderLogs_sublog_do_leader : refined_raft_net_invariant_do_leader leaderLogs_sublog.
Proof using.
unfold refined_raft_net_invariant_do_leader, leaderLogs_sublog.
simpl.
intuition.
repeat find_higher_order_rewrite.
find_copy_apply_lem_hyp doLeader_type.
intuition.
repeat match goal with | [ H : _ |- _ ] => rewrite update_fun_comm with (f := fst) in H | [ H : _ |- _ ] => rewrite update_fun_comm with (f := snd) in H | [ H : _ |- _ ] => rewrite update_fun_comm with (f := leaderLogs) in H end.
rewrite update_fun_comm with (f := snd).
simpl in *.
rewrite update_fun_comm.
rewrite update_nop_ext' by (find_apply_lem_hyp doLeader_same_log; repeat find_rewrite; auto).
find_rewrite_lem update_fun_comm.
match goal with | H : _ |- _ => rewrite update_nop_ext' in H by (repeat find_rewrite; auto) end.
match goal with | H : context [ type ] |- _ => rewrite update_fun_comm in H; rewrite update_nop_ext' in H by (repeat find_rewrite; auto) end.
match goal with | H : _ |- _ => rewrite update_nop_ext' in H by (repeat find_rewrite; auto) end.
eauto.
