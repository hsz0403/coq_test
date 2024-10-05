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

Lemma leaderLogs_candidateEntries_do_leader : refined_raft_net_invariant_do_leader leaderLogs_candidateEntries.
Proof using.
start.
eapply candidateEntries_ext; eauto.
find_higher_order_rewrite.
assert (candidateEntries e (nwState net)).
{
update_destruct; rewrite_update; simpl in *.
-
assert (In (t, ll) (leaderLogs (fst (nwState net h)))) by (repeat find_rewrite; eauto).
eauto.
-
eauto.
}
unfold candidateEntries in *.
break_exists; break_and.
exists x.
update_destruct; rewrite_update; [|auto].
simpl.
split.
-
assert (gd = fst (nwState net h)).
{
repeat find_rewrite.
simpl.
auto.
}
subst.
auto.
-
find_apply_lem_hyp doLeader_type.
break_and.
find_rewrite.
repeat find_rewrite.
auto.
