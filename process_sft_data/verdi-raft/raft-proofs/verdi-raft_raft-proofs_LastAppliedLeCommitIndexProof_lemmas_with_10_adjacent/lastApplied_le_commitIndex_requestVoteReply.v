Require Import VerdiRaft.Raft.
Require Import VerdiRaft.LastAppliedLeCommitIndexInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section LastAppliedLeCommitIndex.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Instance lalcii : lastApplied_le_commitIndex_interface.
split.
auto using lastApplied_le_commitIndex_invariant.
End LastAppliedLeCommitIndex.

Lemma lastApplied_le_commitIndex_appendEntries : raft_net_invariant_append_entries lastApplied_le_commitIndex.
Proof using.
red.
unfold lastApplied_le_commitIndex.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_copy_apply_lem_hyp handleAppendEntries_same_lastApplied.
repeat find_rewrite.
find_apply_lem_hyp handleAppendEntries_log_detailed.
Admitted.

Lemma lastApplied_le_commitIndex_appendEntriesReply : raft_net_invariant_append_entries_reply lastApplied_le_commitIndex.
Proof using.
red.
unfold lastApplied_le_commitIndex.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_copy_apply_lem_hyp handleAppendEntriesReply_same_lastApplied.
repeat find_rewrite.
find_copy_apply_lem_hyp handleAppendEntriesReply_same_commitIndex.
repeat find_rewrite.
Admitted.

Lemma lastApplied_le_commitIndex_requestVote : raft_net_invariant_request_vote lastApplied_le_commitIndex.
Proof using.
red.
unfold lastApplied_le_commitIndex.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_copy_apply_lem_hyp handleRequestVote_same_lastApplied.
repeat find_rewrite.
find_copy_apply_lem_hyp handleRequestVote_same_commitIndex.
repeat find_rewrite.
Admitted.

Lemma doLeader_same_lastApplied: forall st (os : list raft_output) (d' : raft_data) (ms : list (name * msg)) (h0 : name), doLeader st h0 = (os, d', ms) -> lastApplied d' = lastApplied st.
Proof using.
intros.
unfold doLeader, advanceCommitIndex in *.
Admitted.

Lemma fold_left_max : forall l y z, (forall x, In x l -> y <= x) -> y <= z -> y <= fold_left max l z.
Proof using.
induction l; simpl in *; auto.
intros.
specialize (IHl y (max z a)).
forward IHl; eauto.
concludes.
forward IHl; [eapply le_trans; eauto; eauto using Max.le_max_l|].
concludes.
Admitted.

Lemma advanceCommitIndex_commitIndex : forall st h, commitIndex st <= commitIndex (advanceCommitIndex st h).
Proof using.
intros.
unfold advanceCommitIndex.
simpl in *.
apply fold_left_max; auto.
intros.
do_in_map.
subst.
find_apply_lem_hyp filter_In.
Admitted.

Lemma doLeader_same_commitIndex : forall st (os : list raft_output) (d' : raft_data) (ms : list (name * msg)) (h0 : name), doLeader st h0 = (os, d', ms) -> commitIndex st <= commitIndex d'.
Proof using.
intros.
unfold doLeader in *.
repeat break_match; tuple_inversion; auto; eauto using advanceCommitIndex_commitIndex.
Admitted.

Lemma lastApplied_le_commitIndex_doLeader : raft_net_invariant_do_leader lastApplied_le_commitIndex.
Proof using.
red.
unfold lastApplied_le_commitIndex.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_copy_apply_lem_hyp doLeader_same_lastApplied.
find_copy_apply_lem_hyp doLeader_same_commitIndex.
repeat find_rewrite.
Admitted.

Lemma doGenericServer_lastApplied: forall (h : name) (st : raft_data) (out : list raft_output) (st' : raft_data) (ms : list (name * msg)), doGenericServer h st = (out, st', ms) -> lastApplied st' <= max (lastApplied st) (commitIndex st).
Proof using.
intros.
unfold doGenericServer in *.
break_let.
find_inversion.
simpl in *.
break_if; simpl in *; do_bool; auto.
-
use_applyEntries_spec.
subst.
simpl in *.
eauto using Max.le_max_r.
-
use_applyEntries_spec.
subst.
simpl in *.
Admitted.

Lemma lastApplied_le_commitIndex_doGenericServer : raft_net_invariant_do_generic_server lastApplied_le_commitIndex.
Proof using.
red.
unfold lastApplied_le_commitIndex.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_copy_apply_lem_hyp doGenericServer_commitIndex.
find_copy_apply_lem_hyp doGenericServer_lastApplied.
repeat find_rewrite.
Admitted.

Lemma lastApplied_le_commitIndex_clientRequest : raft_net_invariant_client_request lastApplied_le_commitIndex.
Proof using.
red.
unfold lastApplied_le_commitIndex.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_copy_apply_lem_hyp handleClientRequest_commitIndex.
find_copy_apply_lem_hyp handleClientRequest_lastApplied.
repeat find_rewrite.
Admitted.

Lemma lastApplied_le_commitIndex_timeout : raft_net_invariant_timeout lastApplied_le_commitIndex.
Proof using.
red.
unfold lastApplied_le_commitIndex.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_copy_apply_lem_hyp handleTimeout_commitIndex.
find_copy_apply_lem_hyp handleTimeout_lastApplied.
repeat find_rewrite.
Admitted.

Lemma lastApplied_le_commitIndex_reboot : raft_net_invariant_reboot lastApplied_le_commitIndex.
Proof using.
red.
unfold lastApplied_le_commitIndex.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
Admitted.

Lemma lastApplied_le_commitIndex_requestVoteReply : raft_net_invariant_request_vote_reply lastApplied_le_commitIndex.
Proof using.
red.
unfold lastApplied_le_commitIndex.
intros.
simpl in *.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
rewrite handleRequestVoteReply_same_lastApplied.
rewrite handleRequestVoteReply_same_commitIndex.
eauto.
