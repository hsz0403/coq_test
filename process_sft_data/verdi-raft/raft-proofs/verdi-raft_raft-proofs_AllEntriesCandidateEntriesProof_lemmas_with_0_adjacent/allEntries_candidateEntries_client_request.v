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

Lemma allEntries_candidateEntries_client_request : refined_raft_net_invariant_client_request allEntries_candidateEntries.
Proof using cci.
start.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
-
find_copy_apply_lem_hyp update_elections_data_client_request_allEntries.
intuition; repeat find_rewrite; eauto.
+
find_apply_hyp_hyp.
unfold candidateEntries in *.
break_exists_exists.
destruct_update; simpl in *; eauto.
erewrite update_elections_data_client_request_cronies; eauto.
intuition.
find_apply_lem_hyp handleClientRequest_type.
intuition.
repeat find_rewrite.
eauto.
+
break_exists.
intuition.
repeat find_rewrite.
simpl in *.
intuition.
*
find_inversion.
exists h0.
rewrite_update.
simpl.
find_copy_apply_lem_hyp handleClientRequest_type.
break_and; repeat find_rewrite; intuition; try congruence.
erewrite update_elections_data_client_request_cronies; eauto.
eapply won_election_cronies; repeat find_rewrite; eauto using cronies_correct_invariant.
*
find_apply_hyp_hyp.
unfold candidateEntries in *.
break_exists_exists.
destruct_update; simpl in *; eauto.
erewrite update_elections_data_client_request_cronies; eauto.
intuition.
find_apply_lem_hyp handleClientRequest_type.
intuition.
repeat find_rewrite.
eauto.
-
find_apply_hyp_hyp.
unfold candidateEntries in *.
break_exists_exists.
destruct_update; simpl in *; eauto.
erewrite update_elections_data_client_request_cronies; eauto.
intuition.
find_apply_lem_hyp handleClientRequest_type.
intuition.
repeat find_rewrite.
eauto.
