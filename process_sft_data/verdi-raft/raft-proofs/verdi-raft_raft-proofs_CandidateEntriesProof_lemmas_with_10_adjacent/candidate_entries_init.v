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

Lemma doLeader_in_entries : forall (h : name) d h os d' ms m t li pli plt es ci e, doLeader d h = (os, d', ms) -> snd m = AppendEntries t li pli plt es ci -> In m ms -> In e es -> In e (log d).
Proof using.
unfold doLeader.
intros.
repeat break_match; repeat find_inversion; simpl in *; intuition.
do_in_map.
unfold replicaMessage in *.
simpl in *.
subst.
simpl in *.
find_inversion.
Admitted.

Lemma candidate_entries_do_leader : refined_raft_net_invariant_do_leader CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
intros.
intuition; simpl in *.
-
unfold candidateEntries_host_invariant in *.
intros.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update.
+
simpl in *.
find_erewrite_lem doLeader_same_log.
repeat match goal with | [ H : nwState ?net ?h = (_, ?d), H' : context [ log ?d ] |- _ ] => replace (log d) with (log (snd (nwState net h))) in H' by (repeat find_rewrite; auto) end.
eauto using doLeader_preserves_candidateEntries.
+
eauto using doLeader_preserves_candidateEntries.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
find_apply_hyp_hyp.
intuition.
+
eauto using doLeader_preserves_candidateEntries.
+
do_in_map.
subst.
simpl in *.
eapply doLeader_preserves_candidateEntries; eauto.
eapply_prop candidateEntries_host_invariant.
match goal with | [ H : _ |- _ ] => rewrite H end.
simpl.
Admitted.

Lemma doGenericServer_same_type : forall h d os d' ms, doGenericServer h d = (os, d', ms) -> type d' = type d.
Proof using.
unfold doGenericServer.
intros.
Admitted.

Lemma doGenericServer_spec : forall h d os d' ms, doGenericServer h d = (os, d', ms) -> (log d' = log d /\ currentTerm d' = currentTerm d /\ (forall m, In m ms -> ~ is_append_entries (snd m))).
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Lemma doGenericServer_preserves_candidateEntries : forall net gd d h os d' ms e, nwState net h = (gd, d) -> doGenericServer h d = (os, d', ms) -> candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (gd, d')).
Proof using.
intros.
eapply candidateEntries_same; eauto; intros; repeat (rewrite update_fun_comm; simpl in * ); update_destruct; subst; rewrite_update; auto; repeat find_rewrite; simpl; auto.
-
find_copy_apply_lem_hyp doGenericServer_spec.
break_and.
auto.
-
Admitted.

Lemma candidate_entries_do_generic_server : refined_raft_net_invariant_do_generic_server CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
intros.
intuition; simpl in *.
-
unfold candidateEntries_host_invariant in *.
intros.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update.
+
simpl in *.
find_copy_apply_lem_hyp doGenericServer_spec.
break_and.
find_rewrite.
repeat match goal with | [ H : nwState ?net ?h = (_, ?d), H' : context [ log ?d ] |- _ ] => replace (log d) with (log (snd (nwState net h))) in H' by (repeat find_rewrite; auto) end.
eauto using doGenericServer_preserves_candidateEntries.
+
eauto using doGenericServer_preserves_candidateEntries.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
find_apply_hyp_hyp.
intuition.
+
eauto using doGenericServer_preserves_candidateEntries.
+
do_in_map.
find_copy_apply_lem_hyp doGenericServer_spec.
break_and.
subst.
simpl in *.
find_apply_hyp_hyp.
exfalso.
find_rewrite.
Admitted.

Lemma candidate_entries_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
intros.
intuition.
-
unfold candidateEntries_host_invariant in *.
intros.
repeat find_reverse_higher_order_rewrite.
apply candidateEntries_ext with (sigma := nwState net); eauto.
-
unfold candidateEntries_nw_invariant in *.
intros.
find_apply_hyp_hyp.
eapply_prop_hyp In In; eauto.
Admitted.

Lemma reboot_log_same : forall d, log (reboot d) = log d.
Proof using.
unfold reboot.
Admitted.

Lemma reboot_preservers_candidateEntries : forall net h d gd e, nwState net h = (gd, d) -> candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (gd, reboot d)).
Proof using.
unfold reboot, candidateEntries.
intros.
break_exists.
exists x.
break_and.
rewrite update_fun_comm.
simpl in *.
update_destruct; subst; rewrite_update; auto.
repeat find_rewrite.
simpl in *.
intuition.
Admitted.

Lemma candidate_entries_reboot : refined_raft_net_invariant_reboot CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
intros.
intuition.
-
unfold candidateEntries_host_invariant in *.
intros.
repeat find_higher_order_rewrite.
eapply candidateEntries_ext; eauto.
subst.
find_rewrite_lem update_fun_comm.
simpl in *.
find_rewrite_lem update_fun_comm.
simpl in *.
update_destruct; subst; rewrite_update.
+
repeat match goal with | [ H : nwState ?net ?h = (_, ?d), H' : context [ log ?d ] |- _ ] => replace (log d) with (log (snd (nwState net h))) in H' by (repeat find_rewrite; auto) end.
find_apply_hyp_hyp.
eauto using reboot_preservers_candidateEntries.
+
eauto using reboot_preservers_candidateEntries.
-
unfold candidateEntries_nw_invariant in *.
intros.
repeat find_reverse_rewrite.
eapply_prop_hyp In In; eauto.
eapply candidateEntries_ext; eauto.
Admitted.

Theorem candidate_entries_invariant : forall (net : network), refined_raft_intermediate_reachable net -> CandidateEntries net.
Proof using cci cti rri.
intros.
eapply refined_raft_net_invariant; eauto.
-
apply candidate_entries_init.
-
apply candidate_entries_client_request.
-
apply candidate_entries_timeout.
-
apply candidate_entries_append_entries.
-
apply candidate_entries_append_entries_reply.
-
apply candidate_entries_request_vote.
-
apply candidate_entries_request_vote_reply.
-
apply candidate_entries_do_leader.
-
apply candidate_entries_do_generic_server.
-
apply candidate_entries_state_same_packet_subset.
-
Admitted.

Instance cei : candidate_entries_interface.
Proof.
split.
Admitted.

Lemma candidate_entries_init : refined_raft_net_invariant_init CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
unfold candidateEntries_host_invariant, candidateEntries_nw_invariant.
intuition; repeat match goal with | [ H : In _ _ |- _ ] => compute in H end; intuition.
