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

Lemma leaderLogs_candidateEntries_append_entries : refined_raft_net_invariant_append_entries leaderLogs_candidateEntries.
Proof using.
start.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
update_destruct; rewrite_update.
-
simpl in *.
find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
assert (candidateEntries e (nwState net)) by eauto.
unfold candidateEntries in *.
break_exists.
break_and.
exists x.
update_destruct; rewrite_update; [|auto].
simpl.
subst.
rewrite update_elections_data_appendEntries_cronies.
split; [auto|].
find_apply_lem_hyp handleAppendEntries_type_term.
break_or_hyp; break_and.
*
repeat find_rewrite.
auto.
*
unfold not.
intros.
find_rewrite.
discriminate.
-
assert (candidateEntries e (nwState net)) by eauto.
unfold candidateEntries in *.
break_exists.
break_and.
exists x.
update_destruct; rewrite_update; [|auto].
simpl.
subst.
rewrite update_elections_data_appendEntries_cronies.
split; [auto|].
find_apply_lem_hyp handleAppendEntries_type_term.
break_or_hyp; break_and.
*
repeat find_rewrite.
auto.
*
unfold not.
intros.
find_rewrite.
discriminate.
