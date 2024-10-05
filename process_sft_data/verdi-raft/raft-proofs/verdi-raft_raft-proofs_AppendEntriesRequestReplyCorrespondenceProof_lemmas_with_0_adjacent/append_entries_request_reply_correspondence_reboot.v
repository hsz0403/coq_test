Require Import FunctionalExtensionality.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.
Require Import VerdiRaft.AppendEntriesRequestReplyCorrespondenceInterface.
Require Import Verdi.DupDropReordering.
Section AppendEntriesRequestReplyCorrespondence.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Instance aerrci : append_entries_request_reply_correspondence_interface.
split.
intros.
apply raft_net_invariant; auto.
-
exact append_entries_request_reply_correspondence_init.
-
exact append_entries_request_reply_correspondence_client_request.
-
exact append_entries_request_reply_correspondence_timeout.
-
exact append_entries_request_reply_correspondence_append_entries.
-
exact append_entries_request_reply_correspondence_append_entries_reply.
-
exact append_entries_request_reply_correspondence_request_vote.
-
exact append_entries_request_reply_correspondence_request_vote_reply.
-
exact append_entries_request_reply_correspondence_do_leader.
-
exact append_entries_request_reply_correspondence_do_generic_server.
-
exact append_entries_request_reply_correspondence_state_same_packet_subset.
-
exact append_entries_request_reply_correspondence_reboot.
End AppendEntriesRequestReplyCorrespondence.

Lemma append_entries_request_reply_correspondence_reboot : raft_net_invariant_reboot append_entries_request_reply_correspondence.
Proof using.
red.
unfold append_entries_request_reply_correspondence.
intros.
simpl in *.
find_reverse_rewrite.
find_apply_hyp_hyp.
unfold exists_equivalent_network_with_aer in *.
break_exists_name net''.
break_exists_name pli.
break_exists_name plt.
break_exists_name ci.
break_exists_name n.
intuition.
subst.
remember mkNetwork as mkN.
remember mkPacket as mkP.
unfold Net.name in *.
simpl in *.
exists (mkN ((nwPackets net) ++ [mkP (pDst p) (pSrc p) (AppendEntries t n pli plt es ci)]) (nwState net')).
subst.
exists pli,plt,ci,n.
simpl in *; repeat find_rewrite; intuition.
eapply RIR_step_failure with (net0 := net''); [|eapply StepFailure_reboot with (h0 := h) (failed := [h])]; eauto; simpl; repeat find_rewrite; eauto.
f_equal.
apply functional_extensionality.
intros.
repeat find_higher_order_rewrite.
unfold update.
repeat break_if; subst; eauto; congruence.
