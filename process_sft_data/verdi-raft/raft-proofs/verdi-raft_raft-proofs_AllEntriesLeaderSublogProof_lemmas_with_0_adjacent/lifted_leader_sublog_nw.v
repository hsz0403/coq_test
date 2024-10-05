Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.AllEntriesLeaderSublogInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.AllEntriesCandidateEntriesInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.OneLeaderPerTermInterface.
Section AllEntriesLeaderSublog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cei : candidate_entries_interface}.
Context {lsi : leader_sublog_interface}.
Context {olpti : one_leader_per_term_interface}.
Context {aecei : allEntries_candidate_entries_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Hint Resolve map_snd : core.
Instance aelsi : allEntries_leader_sublog_interface.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply allEntries_leader_sublog_init.
-
apply allEntries_leader_sublog_client_request.
-
apply allEntries_leader_sublog_timeout.
-
apply allEntries_leader_sublog_append_entries.
-
apply allEntries_leader_sublog_append_entries_reply.
-
apply allEntries_leader_sublog_request_vote.
-
apply allEntries_leader_sublog_request_vote_reply.
-
apply allEntries_leader_sublog_do_leader.
-
apply allEntries_leader_sublog_do_generic_server.
-
apply allEntries_leader_sublog_state_same_packet_subset.
-
apply allEntries_leader_sublog_reboot.
End AllEntriesLeaderSublog.

Lemma lifted_leader_sublog_nw : forall net p t n pli plt es ci h e, refined_raft_intermediate_reachable net -> In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> type (snd (nwState net h)) = Leader -> eTerm e = currentTerm (snd (nwState net h)) -> In e es -> In e (log (snd (nwState net h))).
Proof using lsi rri.
intros.
pose proof (lift_prop _ leader_sublog_invariant_invariant _ ltac:(eauto)) as Hinv.
unfold leader_sublog_invariant, leader_sublog_nw_invariant in *.
destruct Hinv as [Hhost Hnw].
find_apply_lem_hyp ghost_packet.
eapply_prop_hyp In In; eauto; try find_rewrite_lem deghost_spec; try rewrite deghost_spec; eauto.
