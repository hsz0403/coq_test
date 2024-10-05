Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.CommitRecordedCommittedInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.StateMachineSafetyPrimeInterface.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.LeaderCompletenessInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.PrevLogLeaderSublogInterface.
Require Import VerdiRaft.CurrentTermGtZeroInterface.
Require Import VerdiRaft.LastAppliedLeCommitIndexInterface.
Require Import VerdiRaft.MatchIndexAllEntriesInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.GhostLogCorrectInterface.
Require Import VerdiRaft.GhostLogsLogPropertiesInterface.
Require Import VerdiRaft.GhostLogLogMatchingInterface.
Require Import VerdiRaft.TransitiveCommitInterface.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RaftMsgRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section StateMachineSafetyProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Context {lmi : log_matching_interface}.
Context {smspi : state_machine_safety'interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {pllsi : prevLog_leader_sublog_interface}.
Context {ctgt0 : current_term_gt_zero_interface}.
Context {lalcii : lastApplied_le_commitIndex_interface}.
Context {miaei : match_index_all_entries_interface}.
Context {lhlli : leaders_have_leaderLogs_interface}.
Context {lci : leader_completeness_interface}.
Context {lsi : leader_sublog_interface}.
Context {taifoli : terms_and_indices_from_one_log_interface}.
Context {glci : ghost_log_correct_interface}.
Context {lphogli : log_properties_hold_on_ghost_logs_interface}.
Context {glemi : ghost_log_entries_match_interface}.
Context {tci : transitive_commit_interface}.
Context {tsi : term_sanity_interface}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {rmri : raft_msg_refinement_interface}.
Definition ghost_log_network : Type := @network _ raft_msg_refined_multi_params.
Definition ghost_log_packet : Type := @packet _ raft_msg_refined_multi_params.
Definition lifted_maxIndex_sanity (net : ghost_log_network) : Prop := (forall h, lastApplied (snd (nwState net h)) <= maxIndex (log (snd (nwState net h)))) /\ (forall h, commitIndex (snd (nwState net h)) <= maxIndex (log (snd (nwState net h)))).
Definition lifted_no_entries_past_current_term_host net := forall (h : name) e, In e (log (snd (nwState net h))) -> eTerm e <= currentTerm (snd (nwState net h)).
Definition lifted_entries_contiguous (net : ghost_log_network) : Prop := forall h, contiguous_range_exact_lo (log (snd (nwState net h))) 0.
Definition lifted_entries_contiguous_nw (net : ghost_log_network) : Prop := forall p t n pli plt es ci, In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> contiguous_range_exact_lo es pli.
Definition lifted_entries_gt_0 (net : ghost_log_network) : Prop := forall h e, In e (log (snd (nwState net h))) -> eIndex e > 0.
Definition lifted_directly_committed (net : ghost_log_network) (e : entry) : Prop := exists quorum, NoDup quorum /\ length quorum > div2 (length nodes) /\ (forall h, In h quorum -> In (eTerm e, e) (allEntries (fst (nwState net h)))).
Definition lifted_committed (net : ghost_log_network) (e : entry) (t : term) : Prop := exists h e', eTerm e' <= t /\ lifted_directly_committed net e' /\ eIndex e <= eIndex e' /\ In e (log (snd (nwState net h))) /\ In e' (log (snd (nwState net h))).
Definition commit_invariant_host (net : ghost_log_network) : Prop := forall h e, In e (log (snd (nwState net h))) -> eIndex e <= commitIndex (snd (nwState net h)) -> lifted_committed net e (currentTerm (snd (nwState net h))).
Definition commit_invariant_nw (net : ghost_log_network) : Prop := forall p t lid pli plt es lci e, In p (nwPackets net) -> snd (pBody p) = AppendEntries t lid pli plt es lci -> In e (fst (pBody p)) -> eIndex e <= lci -> lifted_committed net e t.
Definition commit_invariant (net : ghost_log_network) : Prop := commit_invariant_host net /\ commit_invariant_nw net.
Definition lifted_prevLog_leader_sublog (net : network) : Prop := forall leader p t leaderId prevLogIndex prevLogTerm entries leaderCommit, type (snd (nwState net leader)) = Leader -> In p (nwPackets net) -> snd (pBody p) = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> currentTerm (snd (nwState net leader)) = prevLogTerm -> 0 < prevLogIndex -> 0 < prevLogTerm -> exists ple, eIndex ple = prevLogIndex /\ eTerm ple = prevLogTerm /\ In ple (log (snd (nwState net leader))).
Definition lifted_state_machine_safety_nw' net := forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit e t', In p (nwPackets net) -> snd (pBody p) = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> lifted_committed net e t' -> t >= t' -> (prevLogIndex > eIndex e \/ (prevLogIndex = eIndex e /\ prevLogTerm = eTerm e) \/ eIndex e > maxIndex entries \/ In e entries).
Definition lifted_entries_gt_0_nw (net : ghost_log_network) : Prop := forall p t n pli plt es ci e, In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> In e es -> eIndex e > 0.
Definition lifted_entries_sorted_nw' (net : ghost_log_network) := forall p t n pli plt es ci, In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> sorted es.
Definition lifted_leaders_have_leaderLogs_strong (net : ghost_log_network) := forall h, type (snd (nwState net h)) = Leader -> exists ll es, In (currentTerm (snd (nwState net h)), ll) (leaderLogs (fst (nwState net h))) /\ log (snd (nwState net h)) = es ++ ll /\ (forall e : entry, In e es -> eTerm e = currentTerm (snd (nwState net h))).
Definition lifted_one_leaderLog_per_term (net : ghost_log_network) : Prop := forall h h' t ll ll', In (t, ll) (leaderLogs (fst (nwState net h))) -> In (t, ll') (leaderLogs (fst (nwState net h'))) -> h = h' /\ ll = ll'.
Definition lifted_leaders_have_leaderLogs (net : ghost_log_network) : Prop := forall h, type (snd (nwState net h)) = Leader -> exists ll, In (currentTerm (snd (nwState net h)), ll) (leaderLogs (fst (nwState net h))).
Definition lifted_leader_completeness_directly_committed (net : ghost_log_network) : Prop := forall t e log h, lifted_directly_committed net e -> t > eTerm e -> In (t, log) (leaderLogs (fst (nwState net h))) -> In e log.
Definition lifted_leader_completeness_committed (net : ghost_log_network) : Prop := forall t t' e log h, lifted_committed net e t -> t' > t -> In (t', log) (leaderLogs (fst (nwState net h))) -> In e log.
Definition lifted_leader_completeness (net : ghost_log_network) : Prop := lifted_leader_completeness_directly_committed net /\ lifted_leader_completeness_committed net.
Definition msg_lifted_leader_sublog_host (net : ghost_log_network) : Prop := forall leader e h, type (snd (nwState net leader)) = Leader -> In e (log (snd (nwState net h))) -> eTerm e = currentTerm (snd (nwState net leader)) -> In e (log (snd (nwState net leader))).
Definition everything (net : ghost_log_network) : Prop := lifted_maxIndex_sanity net /\ commit_invariant net /\ state_machine_safety (deghost (mgv_deghost net)).
Instance smsi : state_machine_safety_interface.
Proof.
split.
exact state_machine_safety_invariant.
Instance misi : max_index_sanity_interface.
Proof.
split.
exact maxIndex_sanity_invariant.
Instance crci : commit_recorded_committed_interface.
Proof.
split.
intros.
find_apply_lem_hyp commit_recorded_committed_invariant.
unfold commit_invariant, commit_recorded_committed, commit_recorded in *.
intros.
find_rewrite_lem (deghost_spec net h).
intuition; repeat match goal with | [ H : forall _, _, h : entry |- _ ] => specialize (H h) | [ H : forall _, _, h : Net.name |- _ ] => specialize (H h) end; repeat find_rewrite_lem deghost_spec; auto.
End StateMachineSafetyProof.

Lemma doGenericServer_preserves_committed : forall (net net' : ghost_log_network) h out st' ms e t, doGenericServer h (snd (nwState net h)) = (out, st', ms) -> (forall h', nwState net' h' = update name_eq_dec (nwState net) h (fst (nwState net h), st') h') -> lifted_committed net e t -> lifted_committed net' e t.
Proof using rmri.
intros.
eapply lifted_committed_log_allEntries_preserved; eauto; intros; repeat find_higher_order_rewrite; update_destruct_simplify; auto.
Admitted.

Lemma commit_invariant_do_generic_server : msg_refined_raft_net_invariant_do_generic_server commit_invariant.
Proof using rmri.
unfold msg_refined_raft_net_invariant_do_generic_server, commit_invariant.
simpl.
intros.
match goal with | [ H : nwState ?net ?h = (?x, ?y) |- _ ] => replace x with (fst (nwState net h)) in * by (rewrite H; auto); replace y with (snd (nwState net h)) in * by (rewrite H; auto); clear H end.
intuition.
-
unfold commit_invariant_host in *.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify.
+
eapply doGenericServer_preserves_committed; eauto.
match goal with | [ H : context [commitIndex] |- _ ] => erewrite doGenericServer_commitIndex in H by eauto end.
match goal with | [ H : context [log] |- _ ] => erewrite doGenericServer_log in H by eauto end.
eapply lifted_committed_monotonic; eauto.
find_apply_lem_hyp doGenericServer_type.
intuition.
repeat find_rewrite.
auto.
+
eapply doGenericServer_preserves_committed; eauto.
-
unfold commit_invariant_nw in *.
simpl.
intuition.
+
find_apply_hyp_hyp.
intuition.
*
eapply doGenericServer_preserves_committed; eauto.
*
do_in_map.
unfold add_ghost_msg in *.
do_in_map.
find_apply_lem_hyp doGenericServer_packets.
subst.
simpl in *.
Admitted.

Lemma commit_invariant_state_same_packet_subset : msg_refined_raft_net_invariant_state_same_packet_subset commit_invariant.
Proof using rmri.
unfold msg_refined_raft_net_invariant_state_same_packet_subset, commit_invariant.
intuition.
-
unfold commit_invariant_host in *.
intros.
repeat find_reverse_higher_order_rewrite.
destruct net, net'.
simpl in *.
eapply lifted_committed_ext; [|eauto].
simpl.
auto.
-
unfold commit_invariant_nw in *.
intros.
find_apply_hyp_hyp.
destruct net, net'.
simpl in *.
eapply lifted_committed_ext'; [|eauto].
Admitted.

Lemma reboot_preserves_committed : forall (net net' : ghost_log_network) h e t, (forall h', nwState net' h' = update name_eq_dec (nwState net) h (fst (nwState net h), reboot (snd (nwState net h))) h') -> lifted_committed net e t -> lifted_committed net' e t.
Proof using rmri.
unfold reboot.
intros.
Admitted.

Lemma commit_invariant_reboot : msg_refined_raft_net_invariant_reboot commit_invariant.
Proof using rmri.
unfold msg_refined_raft_net_invariant_reboot, commit_invariant.
intros.
match goal with | [ H : nwState ?net ?h = (?x, ?y) |- _ ] => replace x with (fst (nwState net h)) in * by (rewrite H; auto); replace y with (snd (nwState net h)) in * by (rewrite H; auto); clear H end.
intuition.
-
unfold commit_invariant_host in *.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify; eapply reboot_preserves_committed; eauto.
-
unfold commit_invariant_nw in *.
intros.
unfold mgv_refined_base_params, raft_refined_base_params, refined_base_params in *.
simpl in *.
repeat find_reverse_rewrite.
Admitted.

Lemma maxIndex_sanity_lift : forall net, maxIndex_sanity (deghost (mgv_deghost net)) -> lifted_maxIndex_sanity net.
Proof using rmri rri.
unfold maxIndex_sanity, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
intros.
Admitted.

Lemma maxIndex_sanity_lower : forall net, lifted_maxIndex_sanity net -> maxIndex_sanity (deghost (mgv_deghost net)).
Proof using rri.
unfold maxIndex_sanity, lifted_maxIndex_sanity, maxIndex_lastApplied, maxIndex_commitIndex.
Admitted.

Lemma everything_init : msg_refined_raft_net_invariant_init everything.
Proof using rmri lalcii smspi rri.
unfold msg_refined_raft_net_invariant_init, everything.
intuition.
-
apply lifted_maxIndex_sanity_init.
-
apply commit_invariant_init.
-
apply state_machine_safety_deghost.
+
apply commit_invariant_lower_commit_recorded_committed; [constructor|].
apply commit_invariant_init.
+
apply state_machine_safety'_invariant.
Admitted.

Lemma everything_client_request : msg_refined_raft_net_invariant_client_request' everything.
Proof using rmri lalcii smspi si rri.
unfold msg_refined_raft_net_invariant_client_request', everything.
intuition.
-
eapply lifted_maxIndex_sanity_client_request; eauto.
-
eapply commit_invariant_client_request; eauto.
+
auto using maxIndex_sanity_lower.
-
apply state_machine_safety_deghost.
+
apply commit_invariant_lower_commit_recorded_committed; auto.
eapply commit_invariant_client_request; eauto.
apply maxIndex_sanity_lower.
auto.
+
apply state_machine_safety'_invariant.
Admitted.

Lemma everything_timeout : msg_refined_raft_net_invariant_timeout' everything.
Proof using rmri lalcii smspi rri.
unfold msg_refined_raft_net_invariant_timeout', everything.
intuition.
-
eapply lifted_maxIndex_sanity_timeout; eauto.
-
eapply commit_invariant_timeout; eauto.
-
apply state_machine_safety_deghost.
+
apply commit_invariant_lower_commit_recorded_committed.
auto.
eapply commit_invariant_timeout; eauto.
+
apply state_machine_safety'_invariant.
Admitted.

Lemma everything_append_entries_reply : msg_refined_raft_net_invariant_append_entries_reply' everything.
Proof using rmri lalcii smspi rri.
unfold msg_refined_raft_net_invariant_append_entries_reply', everything.
intuition.
-
eapply lifted_maxIndex_sanity_append_entries_reply; eauto.
-
eapply commit_invariant_append_entries_reply; eauto.
-
apply state_machine_safety_deghost.
+
apply commit_invariant_lower_commit_recorded_committed.
auto.
eapply commit_invariant_append_entries_reply; eauto.
+
apply state_machine_safety'_invariant.
Admitted.

Lemma everything_request_vote : msg_refined_raft_net_invariant_request_vote' everything.
Proof using rmri lalcii smspi rri.
unfold msg_refined_raft_net_invariant_request_vote', everything.
intuition.
-
eapply lifted_maxIndex_sanity_request_vote; eauto.
-
eapply commit_invariant_request_vote; eauto.
-
apply state_machine_safety_deghost.
+
apply commit_invariant_lower_commit_recorded_committed.
auto.
eapply commit_invariant_request_vote; eauto.
+
apply state_machine_safety'_invariant.
Admitted.

Lemma everything_request_vote_reply : msg_refined_raft_net_invariant_request_vote_reply' everything.
Proof using rmri lalcii smspi rri.
unfold msg_refined_raft_net_invariant_request_vote_reply', everything.
intuition.
-
eapply lifted_maxIndex_sanity_request_vote_reply; eauto.
-
eapply commit_invariant_request_vote_reply; eauto.
-
apply state_machine_safety_deghost.
+
apply commit_invariant_lower_commit_recorded_committed.
auto.
eapply commit_invariant_request_vote_reply; eauto.
+
apply state_machine_safety'_invariant.
Admitted.

Lemma everything_do_leader : msg_refined_raft_net_invariant_do_leader' everything.
Proof using rmri miaei lalcii smspi si rri.
unfold msg_refined_raft_net_invariant_do_leader', everything.
intuition.
-
eapply lifted_maxIndex_sanity_do_leader; eauto.
-
eapply commit_invariant_do_leader; eauto.
-
apply state_machine_safety_deghost.
+
apply commit_invariant_lower_commit_recorded_committed.
auto.
eapply commit_invariant_do_leader; eauto.
+
apply state_machine_safety'_invariant.
Admitted.

Lemma everything_do_generic_server : msg_refined_raft_net_invariant_do_generic_server' everything.
Proof using rmri lalcii smspi rri.
unfold msg_refined_raft_net_invariant_do_generic_server', everything.
intuition.
-
eapply lifted_maxIndex_sanity_do_generic_server; eauto.
-
eapply commit_invariant_do_generic_server; eauto.
-
apply state_machine_safety_deghost.
+
apply commit_invariant_lower_commit_recorded_committed.
auto.
eapply commit_invariant_do_generic_server; eauto.
+
apply state_machine_safety'_invariant.
Admitted.

Lemma directly_committed_state_same : forall net net' e, (forall h, nwState net' h = nwState net h) -> directly_committed net e -> directly_committed net' e.
Proof using.
unfold directly_committed.
intuition.
break_exists_exists.
intuition.
find_higher_order_rewrite.
Admitted.

Lemma lifted_committed_state_same : forall (net net' : ghost_log_network) e t, (forall h, nwState net' h = nwState net h) -> lifted_committed net e t -> lifted_committed net' e t.
Proof using rmri.
intuition.
destruct net, net'.
simpl in *.
Admitted.

Lemma exists_in_mgv_deghost_packet : forall (p : packet (params := raft_refined_multi_params)) (net : ghost_log_network), In p (nwPackets (mgv_deghost net)) -> exists q, In q (nwPackets net) /\ pDst q = pDst p /\ pSrc q = pSrc p /\ snd (pBody q) = pBody p.
Proof using.
unfold mgv_deghost.
simpl.
intros.
do_in_map.
subst.
simpl.
Admitted.

Lemma state_machine_safety'_state_same_packet_subset : msg_refined_raft_net_invariant_state_same_packet_subset (fun net : ghost_log_network => state_machine_safety' (mgv_deghost net)).
Proof using rmri.
unfold msg_refined_raft_net_invariant_state_same_packet_subset, state_machine_safety'.
intuition.
-
unfold state_machine_safety_host' in *.
intuition.
repeat find_apply_lem_hyp committed_lifted_committed.
eauto 6 using lifted_committed_committed, lifted_committed_state_same.
-
unfold state_machine_safety_nw' in *.
intuition.
find_apply_lem_hyp exists_in_mgv_deghost_packet.
break_exists.
break_and.
find_apply_hyp_hyp.
find_apply_lem_hyp in_mgv_ghost_packet.
match goal with | [ H : context [ pBody ] |- _ ] => eapply H; eauto end.
+
rewrite pBody_mgv_deghost_packet.
repeat find_rewrite.
eauto.
+
apply lifted_committed_committed.
Admitted.

Lemma CRC_state_same_packet_subset : msg_refined_raft_net_invariant_state_same_packet_subset (fun net : ghost_log_network => commit_recorded_committed (mgv_deghost net)).
Proof using rri.
unfold msg_refined_raft_net_invariant_state_same_packet_subset, commit_recorded_committed, commit_recorded, committed, directly_committed.
intros.
specialize (H1 h e).
repeat find_rewrite_lem deghost_spec.
repeat find_rewrite_lem msg_deghost_spec'.
repeat find_higher_order_rewrite.
find_apply_hyp_hyp.
break_exists_exists.
repeat find_rewrite_lem msg_deghost_spec'.
repeat rewrite msg_deghost_spec'.
repeat find_higher_order_rewrite.
intuition.
break_exists_exists.
intuition.
find_apply_hyp_hyp.
repeat find_rewrite_lem msg_deghost_spec'.
repeat rewrite msg_deghost_spec'.
repeat find_higher_order_rewrite.
Admitted.

Lemma everything_append_entries : msg_refined_raft_net_invariant_append_entries' everything.
Proof using rmri tsi glemi lphogli glci lalcii rlmli smspi si rri.
unfold msg_refined_raft_net_invariant_append_entries', everything.
intuition.
-
eapply lifted_maxIndex_sanity_append_entries; eauto.
intros.
find_apply_hyp_hyp.
intuition.
right.
subst.
unfold mgv_deghost_packet.
auto.
-
eapply commit_invariant_append_entries; eauto.
-
apply state_machine_safety_deghost.
+
apply commit_invariant_lower_commit_recorded_committed.
auto.
eapply commit_invariant_append_entries; eauto.
+
apply state_machine_safety'_invariant.
auto using msg_simulation_1.
