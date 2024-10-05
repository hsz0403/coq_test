Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CroniesTermInterface.
Section CroniesTermProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Instance cti : cronies_term_interface.
Proof.
split.
auto using cronies_term_invariant.
End CroniesTermProof.

Lemma handleClientRequest_spec : forall h st client id c out st' l, handleClientRequest h st client id c = (out, st', l) -> currentTerm st' = currentTerm st.
Proof using.
intros.
unfold handleClientRequest in *.
Admitted.

Lemma cronies_term_client_request : refined_raft_net_invariant_client_request cronies_term.
Proof using.
unfold refined_raft_net_invariant_client_request, cronies_term, update_elections_data_client_request in *.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
find_apply_lem_hyp handleClientRequest_spec.
repeat find_rewrite.
Admitted.

Lemma cronies_term_timeout : refined_raft_net_invariant_timeout cronies_term.
Proof using.
unfold refined_raft_net_invariant_timeout, cronies_term.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
find_eapply_lem_hyp handleTimeout_spec; eauto.
intuition.
Admitted.

Lemma doLeader_spec : forall st h os st' ms, doLeader st h = (os, st', ms) -> currentTerm st' = currentTerm st.
Proof using.
intros.
unfold doLeader in *.
Admitted.

Lemma cronies_term_do_leader : refined_raft_net_invariant_do_leader cronies_term.
Proof using.
unfold refined_raft_net_invariant_do_leader, cronies_term.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
find_apply_lem_hyp doLeader_spec.
repeat find_rewrite.
Admitted.

Lemma doGenericServer_spec : forall st h os st' ms, doGenericServer h st = (os, st', ms) -> currentTerm st' = currentTerm st.
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Lemma cronies_term_do_generic_server : refined_raft_net_invariant_do_generic_server cronies_term.
Proof using.
unfold refined_raft_net_invariant_do_generic_server, cronies_term.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
find_apply_lem_hyp doGenericServer_spec.
repeat find_rewrite.
Admitted.

Lemma handleAppendEntries_spec : forall h st t n pli plt es ci st' m, handleAppendEntries h st t n pli plt es ci = (st', m) -> currentTerm st <= currentTerm st'.
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Lemma update_elections_data_appendEntries_spec : forall h st t n pli plt es ci st' e t', update_elections_data_appendEntries h st t n pli plt es ci = st' -> In e (cronies st' t') -> In e (cronies (fst st) t').
Proof using.
intros.
unfold update_elections_data_appendEntries in *.
Admitted.

Lemma cronies_term_append_entries : refined_raft_net_invariant_append_entries cronies_term.
Proof using.
unfold refined_raft_net_invariant_append_entries, cronies_term.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
find_apply_lem_hyp handleAppendEntries_spec.
find_eapply_lem_hyp update_elections_data_appendEntries_spec; eauto.
Admitted.

Lemma handleAppendEntriesReply_spec : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> currentTerm st <= currentTerm st'.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma cronies_term_append_entries_reply : refined_raft_net_invariant_append_entries_reply cronies_term.
Proof using.
unfold refined_raft_net_invariant_append_entries_reply, cronies_term.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
find_apply_lem_hyp handleAppendEntriesReply_spec.
Admitted.

Lemma handleTimeout_spec : forall h st out st' l t h', handleTimeout h (snd st) = (out, st', l) -> In h' (cronies (update_elections_data_timeout h st) t) -> (currentTerm (snd st) <= currentTerm st' /\ (In h' (cronies (fst st) t) \/ t = currentTerm st')).
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader, update_elections_data_timeout in *.
repeat (break_match; repeat find_inversion; simpl in *; auto); intuition; unfold handleTimeout, tryToBecomeLeader in *; repeat (break_match; repeat find_inversion; simpl in *; auto); congruence.
