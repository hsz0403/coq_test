Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RaftMsgRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.GhostLogCorrectInterface.
Require Import VerdiRaft.GhostLogsLogPropertiesInterface.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.AllEntriesLeaderSublogInterface.
Require Import VerdiRaft.GhostLogAllEntriesInterface.
Require Import VerdiRaft.GhostLogLogMatchingInterface.
Section GhostLogLogMatching.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rmri : raft_msg_refinement_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {glci : ghost_log_correct_interface}.
Context {lphogli : log_properties_hold_on_ghost_logs_interface}.
Context {tsi : term_sanity_interface}.
Context {aelsi : allEntries_leader_sublog_interface}.
Context {glaei : ghost_log_allEntries_interface}.
Definition ghost_log_entries_match_nw (net : network) : Prop := forall p p', In p (nwPackets net) -> In p' (nwPackets net) -> entries_match (fst (pBody p)) (fst (pBody p')).
Definition ghost_log_entries_match (net : network) : Prop := ghost_log_entries_match_host net /\ ghost_log_entries_match_nw net.
Definition lifted_entries_contiguous net := forall h, contiguous_range_exact_lo (log (snd (nwState net h))) 0.
Definition lifted_entries_sorted net := forall h, sorted (log (snd (nwState net h))).
Definition lifted_entries_contiguous_nw net := forall p t n pli plt es ci, In p (nwPackets net) -> snd (pBody p) = AppendEntries t n pli plt es ci -> contiguous_range_exact_lo es pli.
Definition lifted_entries_match net := forall h h', entries_match (log (snd (nwState net h))) (log (snd (nwState net h'))).
Definition lifted_no_entries_past_current_term_host net := forall (h : name) e, In e (log (snd (nwState net h))) -> eTerm e <= currentTerm (snd (nwState net h)).
Definition lifted_allEntries_leader_sublog (net : network) := forall leader e h, type (snd (nwState net leader)) = Leader -> In e (map snd (allEntries (fst (nwState net h)))) -> eTerm e = currentTerm (snd (nwState net leader)) -> In e (log (snd (nwState net leader))).
Hint Resolve entries_match_refl : core.
Hint Resolve entries_match_sym : core.
Ltac packet_simpl := first [do_in_map; subst; simpl in *; unfold add_ghost_msg in *; do_in_map; subst; simpl in *|subst; simpl in *].
Arguments write_ghost_log / _ _ _ _ _.
Instance glemi : ghost_log_entries_match_interface.
Proof.
split.
apply ghost_log_entries_match_invariant.
End GhostLogLogMatching.

Lemma ghost_log_entries_match_append_entries_reply : msg_refined_raft_net_invariant_append_entries_reply ghost_log_entries_match.
Proof using rlmli rmri.
red.
split; red; intros; simpl in *; intuition; unfold ghost_log_entries_match in *; break_and.
-
repeat find_higher_order_rewrite; destruct_update; simpl in *; eauto.
+
find_apply_hyp_hyp.
intuition.
*
erewrite handleAppendEntriesReply_log; eauto.
*
packet_simpl.
apply entries_match_refl.
+
find_apply_hyp_hyp.
intuition.
*
eauto.
*
packet_simpl.
erewrite handleAppendEntriesReply_log with (st'0 := d) by eauto.
eapply lifted_entries_match_invariant; eauto.
-
find_apply_hyp_hyp.
find_apply_hyp_hyp.
intuition.
+
eauto.
+
subst.
simpl in *.
do_in_map.
subst.
simpl in *.
unfold add_ghost_msg in *.
do_in_map.
subst.
simpl in *.
erewrite handleAppendEntriesReply_same_log by eauto.
eauto.
+
subst.
simpl in *.
do_in_map.
subst.
simpl in *.
unfold add_ghost_msg in *.
do_in_map.
subst.
simpl in *.
erewrite handleAppendEntriesReply_same_log by eauto.
eauto.
+
subst.
simpl in *.
repeat do_in_map.
subst.
simpl in *.
unfold add_ghost_msg in *.
repeat do_in_map.
subst.
simpl in *.
auto.
