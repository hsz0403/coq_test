Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.LeaderLogsCandidateEntriesInterface.
Section CandidateEntriesInterface.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cci : cronies_correct_interface}.
Context {cti : cronies_term_interface}.
Context {cei : candidate_entries_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Ltac start := red; unfold leaderLogs_candidateEntries; simpl; intros.
Instance llcei : leaderLogs_candidate_entries_interface.
Proof.
constructor.
exact leaderLogs_candidateEntries_invariant.
End CandidateEntriesInterface.

Lemma leaderLogs_candidateEntries_request_vote : refined_raft_net_invariant_request_vote leaderLogs_candidateEntries.
Proof using.
start.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
assert (candidateEntries e (nwState net)).
{
update_destruct; rewrite_update; simpl in *.
-
find_rewrite_lem leaderLogs_update_elections_data_requestVote.
eauto.
-
eauto.
}
unfold candidateEntries in *.
break_exists.
break_and.
exists x.
update_destruct; rewrite_update; simpl; [|auto].
subst.
split.
-
rewrite update_elections_data_requestVote_cronies.
auto.
-
find_apply_lem_hyp handleRequestVote_type_term.
break_or_hyp; break_and.
+
repeat find_rewrite.
auto.
+
unfold not.
intros.
find_rewrite.
discriminate.
