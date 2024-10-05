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

Lemma allEntries_candidateEntries_request_vote_reply : refined_raft_net_invariant_request_vote_reply allEntries_candidateEntries.
Proof using cei cci.
start.
intro_refined_invariant candidate_entries_invariant.
eapply candidateEntries_ext; eauto.
subst.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
destruct_update.
-
find_rewrite_lem update_elections_data_requestVoteReply_allEntries; eauto.
find_apply_hyp_hyp.
eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
-
eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
