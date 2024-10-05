Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CandidateEntriesInterface.
Section CandidateEntriesProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cti : cronies_term_interface}.
Context {tsi : term_sanity_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Instance cei : candidate_entries_interface.
Proof.
split.
auto using candidate_entries_invariant.
End CandidateEntriesProof.

Lemma candidate_entries_request_vote_reply : refined_raft_net_invariant_request_vote_reply CandidateEntries.
Proof using cci.
red.
unfold CandidateEntries.
intros.
intuition.
-
unfold candidateEntries_host_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
update_destruct.
+
subst.
rewrite_update.
match goal with | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] => remember (handleRequestVoteReply h st h' t r) as new_state end.
find_copy_apply_lem_hyp handleRequestVoteReply_spec.
break_and.
match goal with | H : log _ = log _ |- _ => rewrite H in * end.
find_apply_hyp_hyp.
eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
+
rewrite_update.
eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
eapply handleRequestVoteReply_preserves_candidate_entries; eauto.
