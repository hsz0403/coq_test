Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.NoAppendEntriesRepliesToSelfInterface.
Require Import VerdiRaft.NoAppendEntriesToSelfInterface.
Section NoAppendEntriesRepliesToSelf.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {naetsi : no_append_entries_to_self_interface}.
Instance noaertsi : no_append_entries_replies_to_self_interface.
split.
auto using no_append_entries_replies_to_self_invariant.
End NoAppendEntriesRepliesToSelf.

Lemma doLeader_no_messages_to_self : forall st h os st' ms m, doLeader st h = (os, st', ms) -> In m ms -> fst m <> h.
Proof using.
intros.
unfold doLeader in *.
repeat break_match; try solve [find_inversion; simpl in *; congruence].
find_inversion.
do_in_map.
subst.
simpl in *.
find_apply_lem_hyp filter_In.
intuition.
subst.
Admitted.

Lemma no_append_entries_replies_to_self_do_leader : raft_net_invariant_do_leader no_append_entries_replies_to_self.
Proof using.
red.
red.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
do_in_map.
subst.
simpl in *.
Admitted.

Lemma no_append_entries_replies_to_self_do_generic_server : raft_net_invariant_do_generic_server no_append_entries_replies_to_self.
Proof using.
red.
red.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp doGenericServer_packets.
subst.
simpl in *.
Admitted.

Lemma no_append_entries_replies_to_self_append_entries_reply : raft_net_invariant_append_entries_reply no_append_entries_replies_to_self.
Proof using.
red.
red.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
do_in_map.
subst.
simpl in *.
find_apply_lem_hyp handleAppendEntriesReply_packets.
subst.
Admitted.

Lemma no_append_entries_replies_to_self_request_vote : raft_net_invariant_request_vote no_append_entries_replies_to_self.
Proof using.
red.
red.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
subst.
simpl in *.
subst.
unfold handleRequestVote in *.
Admitted.

Lemma no_append_entries_replies_to_self_request_vote_reply : raft_net_invariant_request_vote_reply no_append_entries_replies_to_self.
Proof using.
red.
red.
intros.
simpl in *.
find_apply_hyp_hyp.
Admitted.

Lemma no_append_entries_replies_to_self_client_request : raft_net_invariant_client_request no_append_entries_replies_to_self.
Proof using.
red.
red.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
do_in_map.
subst.
simpl in *.
Admitted.

Lemma no_append_entries_replies_to_self_timeout : raft_net_invariant_timeout no_append_entries_replies_to_self.
Proof using.
red.
red.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
do_in_map.
subst.
simpl in *.
match goal with | H : fst _ = _ |- _ => clear H end.
Admitted.

Lemma no_append_entries_replies_to_self_state_same_packet_subset : raft_net_invariant_state_same_packet_subset no_append_entries_replies_to_self.
Proof using.
red.
red.
intros.
simpl in *.
find_apply_hyp_hyp.
Admitted.

Lemma no_append_entries_replies_to_self_reboot : raft_net_invariant_reboot no_append_entries_replies_to_self.
Proof using.
red.
red.
intros.
simpl in *.
find_reverse_rewrite.
Admitted.

Lemma no_append_entries_replies_to_self_init : raft_net_invariant_init no_append_entries_replies_to_self.
Proof using.
red.
red.
intros.
simpl in *.
Admitted.

Theorem no_append_entries_replies_to_self_invariant : forall net, raft_intermediate_reachable net -> no_append_entries_replies_to_self net.
Proof using naetsi.
intros.
apply raft_net_invariant; auto.
-
apply no_append_entries_replies_to_self_init.
-
apply no_append_entries_replies_to_self_client_request.
-
apply no_append_entries_replies_to_self_timeout.
-
apply no_append_entries_replies_to_self_append_entries.
-
apply no_append_entries_replies_to_self_append_entries_reply.
-
apply no_append_entries_replies_to_self_request_vote.
-
apply no_append_entries_replies_to_self_request_vote_reply.
-
apply no_append_entries_replies_to_self_do_leader.
-
apply no_append_entries_replies_to_self_do_generic_server.
-
apply no_append_entries_replies_to_self_state_same_packet_subset.
-
Admitted.

Instance noaertsi : no_append_entries_replies_to_self_interface.
split.
Admitted.

Lemma no_append_entries_replies_to_self_append_entries : raft_net_invariant_append_entries no_append_entries_replies_to_self.
Proof using naetsi.
red.
red.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
subst.
simpl in *.
subst.
find_eapply_lem_hyp no_append_entries_to_self_invariant; eauto.
