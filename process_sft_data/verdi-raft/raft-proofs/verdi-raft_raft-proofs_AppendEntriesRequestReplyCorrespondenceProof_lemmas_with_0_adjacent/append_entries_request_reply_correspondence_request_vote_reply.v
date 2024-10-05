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

Lemma append_entries_request_reply_correspondence_request_vote_reply : raft_net_invariant_request_vote_reply append_entries_request_reply_correspondence.
Proof using.
red.
unfold append_entries_request_reply_correspondence.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
copy_eapply_prop_hyp pBody pBody; auto; [|repeat find_rewrite; in_crush].
unfold exists_equivalent_network_with_aer in *.
break_exists_name net'.
break_exists_name pli'.
break_exists_name plt'.
break_exists_name ci'.
break_exists_name n'.
intuition.
remember mkNetwork as mkN.
remember mkPacket as mkP.
unfold Net.name in *.
simpl in *.
exists (mkN (ps' ++ [mkP (pDst p0) (pSrc p0) (AppendEntries t0 n' pli' plt' es ci')]) st').
subst.
exists pli',plt',ci',n'.
simpl in *; intuition.
repeat find_rewrite.
match goal with | H : nwPackets net' = (?xs ++ ?p :: ?ys) ++ ?l |- _ => assert (nwPackets net' = xs ++ p :: (ys ++ l)) by (find_rewrite_lem app_ass; rewrite app_comm_cons; auto); clear H end.
eapply RIR_handleMessage with (net0 := net') (p1 := p); simpl; repeat find_rewrite; eauto; simpl; repeat break_let; eauto; try find_inversion; eauto.
intros.
do_in_app.
simpl in *.
intuition; try find_apply_hyp_hyp; intuition; in_crush.
