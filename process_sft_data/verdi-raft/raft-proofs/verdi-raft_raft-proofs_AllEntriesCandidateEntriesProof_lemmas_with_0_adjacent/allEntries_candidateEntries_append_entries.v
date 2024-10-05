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

Lemma allEntries_candidateEntries_append_entries : refined_raft_net_invariant_append_entries allEntries_candidateEntries.
Proof using cei.
start.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
destruct_update.
-
simpl in *.
find_eapply_lem_hyp update_elections_data_appendEntries_allEntries_term'; eauto.
intuition.
+
find_apply_hyp_hyp.
unfold candidateEntries in *.
break_exists_exists.
destruct_update; [|auto].
simpl.
subst.
rewrite update_elections_data_appendEntries_cronies.
find_copy_apply_lem_hyp handleAppendEntries_type_term.
intuition; repeat find_rewrite; auto; congruence.
+
subst.
find_eapply_lem_hyp candidate_entries_invariant; eauto.
unfold candidateEntries in *.
break_exists_exists.
destruct_update; [|auto].
simpl.
subst.
rewrite update_elections_data_appendEntries_cronies.
find_copy_apply_lem_hyp handleAppendEntries_type_term.
intuition; repeat find_rewrite; auto; congruence.
-
find_apply_hyp_hyp.
unfold candidateEntries in *.
break_exists_exists.
destruct_update; [|auto].
simpl.
subst.
rewrite update_elections_data_appendEntries_cronies.
find_copy_apply_lem_hyp handleAppendEntries_type_term.
intuition; repeat find_rewrite; auto; congruence.
