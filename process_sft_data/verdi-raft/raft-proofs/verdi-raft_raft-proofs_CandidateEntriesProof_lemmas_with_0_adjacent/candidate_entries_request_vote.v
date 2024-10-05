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

Lemma candidate_entries_request_vote : refined_raft_net_invariant_request_vote CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
intros.
subst.
intuition; simpl in *.
-
unfold candidateEntries_host_invariant in *.
intros.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
find_rewrite_lem update_fun_comm.
simpl in *.
update_destruct; subst; rewrite_update; simpl in *; try find_erewrite_lem handleRequestVote_same_log; eapply handleRequestVote_preserves_candidateEntries; eauto.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
find_apply_hyp_hyp.
intuition.
+
eauto using handleRequestVote_preserves_candidateEntries.
+
subst.
simpl in *.
find_apply_lem_hyp handleRequestVote_only_sends_RVR.
subst.
break_exists.
discriminate.
