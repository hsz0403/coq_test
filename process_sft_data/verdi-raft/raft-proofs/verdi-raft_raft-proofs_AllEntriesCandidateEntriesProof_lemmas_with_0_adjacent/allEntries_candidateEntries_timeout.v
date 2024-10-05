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

Lemma allEntries_candidateEntries_timeout : refined_raft_net_invariant_timeout allEntries_candidateEntries.
Proof using cti.
start.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
assert (candidateEntries e (nwState net)).
{
destruct_update; simpl in *.
-
find_rewrite_lem update_elections_data_timeout_allEntries.
eauto.
-
eauto.
}
unfold candidateEntries in *.
break_exists; break_and.
exists x.
update_destruct; rewrite_update; simpl in *; [|auto].
subst.
split.
-
assert (H100 := update_elections_data_timeout_cronies x (nwState net x) (eTerm e)).
intuition.
+
find_rewrite.
auto.
+
exfalso.
find_apply_lem_hyp wonElection_exists_voter.
break_exists.
find_apply_lem_hyp in_dedup_was_in.
intro_refined_invariant cronies_term_invariant.
eapply_prop_hyp cronies_term In.
simpl in *.
omega.
-
find_apply_lem_hyp handleTimeout_type_strong.
break_or_hyp; break_and.
+
repeat find_rewrite.
auto.
+
intros.
find_rewrite.
exfalso.
find_apply_lem_hyp wonElection_exists_voter.
break_exists.
find_apply_lem_hyp in_dedup_was_in.
intro_refined_invariant cronies_term_invariant.
eapply_prop_hyp cronies_term In.
simpl in *.
omega.
