Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.AllEntriesTermSanityInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.AllEntriesCandidateEntriesInterface.
Section AllEntriesCandidateEntries.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cci : cronies_correct_interface}.
Context {cti : cronies_term_interface}.
Context {cei : candidate_entries_interface}.
Context {lltsi : allEntries_term_sanity_interface}.
Ltac start := red; unfold allEntries_candidateEntries; simpl; intros.
Instance aecei : allEntries_candidate_entries_interface.
Proof.
constructor.
exact allEntries_candidateEntries_invariant.
End AllEntriesCandidateEntries.

Lemma allEntries_candidateEntries_request_vote : refined_raft_net_invariant_request_vote allEntries_candidateEntries.
Proof using.
start.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
assert (candidateEntries e (nwState net)).
{
destruct_update; simpl in *.
-
find_rewrite_lem update_elections_data_requestVote_allEntries.
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
