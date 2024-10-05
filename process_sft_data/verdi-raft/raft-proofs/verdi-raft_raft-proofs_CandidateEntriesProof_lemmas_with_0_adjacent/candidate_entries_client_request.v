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

Lemma candidate_entries_client_request : refined_raft_net_invariant_client_request CandidateEntries.
Proof using cci.
unfold refined_raft_net_invariant_client_request, CandidateEntries.
intros.
subst.
intuition.
-
unfold candidateEntries_host_invariant in *.
intros; simpl in *.
eapply candidateEntries_ext; try eassumption.
repeat find_higher_order_rewrite.
unfold update_elections_data_client_request in *.
repeat break_let.
simpl in *.
destruct (name_eq_dec h0 h); subst.
+
rewrite_update.
unfold update_elections_data_client_request in *.
repeat break_let.
simpl in *.
simpl in *.
find_inversion.
find_apply_lem_hyp handleClientRequest_spec; intuition eauto.
find_apply_hyp_hyp.
intuition.
*
rewrite_update.
eapply candidateEntries_same; eauto; intuition; destruct (name_eq_dec h0 h); subst; rewrite_update; auto.
repeat break_match; simpl; auto.
*
find_apply_lem_hyp cronies_correct_invariant.
unfold candidateEntries.
exists h.
intuition; rewrite_update; simpl in *; try congruence.
repeat find_rewrite.
simpl in *.
repeat break_match; simpl; eauto using won_election_cronies.
+
rewrite_update.
find_apply_lem_hyp handleClientRequest_spec.
eapply candidateEntries_same; eauto; intuition; destruct (name_eq_dec h1 h); subst; rewrite_update; auto; tuple_inversion; repeat find_rewrite; repeat break_match; simpl; auto.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; try eassumption.
find_apply_lem_hyp handleClientRequest_spec.
intuition.
subst.
simpl in *.
eapply_prop_hyp candidateEntries AppendEntries; eauto.
+
eapply candidateEntries_same; eauto; intuition; destruct (name_eq_dec h h0); subst; rewrite_update; auto.
unfold update_elections_data_client_request; repeat break_match; simpl; auto.
+
find_apply_hyp_hyp.
intuition.
