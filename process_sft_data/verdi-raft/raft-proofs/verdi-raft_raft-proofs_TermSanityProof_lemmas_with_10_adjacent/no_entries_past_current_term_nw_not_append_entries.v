Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.TermSanityInterface.
Section TermSanityProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Instance tsi : term_sanity_interface.
Proof.
split.
auto using no_entries_past_current_term_invariant.
End TermSanityProof.

Theorem no_entries_past_current_term_nw_packets_unchanged : forall net ps' st', no_entries_past_current_term_nw net -> (forall p, In p ps' -> In p (nwPackets net) \/ False) -> no_entries_past_current_term_nw (mkNetwork ps' st').
Proof using.
unfold no_entries_past_current_term_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
Admitted.

Theorem no_entries_past_current_term_nw_only_new_packets_matter : forall net ps' l st', no_entries_past_current_term_nw net -> (forall p, In p ps' -> In p (nwPackets net) \/ In p l) -> no_entries_past_current_term_nw (mkNetwork l st') -> no_entries_past_current_term_nw (mkNetwork ps' st').
Proof using.
unfold no_entries_past_current_term_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
Admitted.

Theorem no_entries_past_current_term_nw_no_append_entries : forall net ps' h l st', no_entries_past_current_term_nw net -> (forall p, In p ps' -> In p (nwPackets net) \/ In p (send_packets h l)) -> (forall m, In m l -> ~ is_append_entries (snd m)) -> no_entries_past_current_term_nw (mkNetwork ps' st').
Proof using.
intros.
eapply no_entries_past_current_term_nw_only_new_packets_matter; eauto.
unfold no_entries_past_current_term_nw.
intros.
simpl in *.
do_in_map.
subst.
simpl in *.
find_apply_hyp_hyp.
exfalso.
match goal with H : _ |- _ => apply H end.
Admitted.

Theorem no_entries_past_current_term_init : raft_net_invariant_init (no_entries_past_current_term).
Proof using.
unfold raft_net_invariant_init, no_entries_past_current_term.
intuition.
-
unfold no_entries_past_current_term_host.
intros.
simpl in *.
intuition.
-
unfold no_entries_past_current_term_nw.
intros.
simpl in *.
Admitted.

Lemma doLeader_spec : forall h st os st' ps, doLeader st h = (os, st', ps) -> log st' = log st /\ currentTerm st' = currentTerm st.
Proof using.
intros.
unfold doLeader in *.
Admitted.

Theorem no_entries_past_current_term_do_leader : raft_net_invariant_do_leader (no_entries_past_current_term).
Proof using.
unfold raft_net_invariant_do_leader, no_entries_past_current_term.
intuition.
-
unfold no_entries_past_current_term_host in *.
intros.
simpl in *.
find_apply_lem_hyp doLeader_spec.
find_higher_order_rewrite.
break_if; subst; intuition; repeat find_rewrite; eauto.
-
unfold no_entries_past_current_term_nw in *.
intros; simpl in *.
find_apply_hyp_hyp.
intuition eauto.
unfold doLeader in *.
repeat break_match; repeat find_inversion; try solve_by_inversion.
repeat do_in_map; subst; simpl in *; find_inversion.
find_apply_lem_hyp findGtIndex_in.
Admitted.

Lemma doGenericServer_spec : forall h d os d' ms, doGenericServer h d = (os, d', ms) -> (log d' = log d /\ currentTerm d' = currentTerm d /\ (forall m, In m ms -> ~ is_append_entries (snd m))).
Proof using.
intros.
unfold doGenericServer in *.
Admitted.

Lemma no_entries_past_current_term_do_generic_server : raft_net_invariant_do_generic_server no_entries_past_current_term.
Proof using.
unfold raft_net_invariant_do_generic_server, no_entries_past_current_term.
intros.
find_apply_lem_hyp doGenericServer_spec.
intuition.
-
unfold no_entries_past_current_term_host in *.
intros.
simpl in *.
find_higher_order_rewrite; break_match; eauto.
subst; repeat find_rewrite; eauto.
-
Admitted.

Lemma handleClientRequest_messages : forall h d client id c os d' ms, handleClientRequest h d client id c = (os, d', ms) -> (forall m, In m ms -> ~ is_append_entries (snd m)).
Proof using.
intros.
unfold handleClientRequest in *.
Admitted.

Lemma no_entries_past_current_term_client_request : raft_net_invariant_client_request (no_entries_past_current_term).
Proof using.
unfold raft_net_invariant_client_request, no_entries_past_current_term.
intuition.
-
unfold no_entries_past_current_term_host in *.
intros.
simpl in *.
find_higher_order_rewrite; break_if; eauto.
unfold handleClientRequest in *.
subst.
break_match; find_inversion; eauto.
simpl in *.
intuition.
subst; simpl in *; auto.
-
Admitted.

Lemma handleTimeout_spec : forall h d os d' ms, handleTimeout h d = (os, d', ms) -> log d' = log d /\ currentTerm d <= currentTerm d' /\ ( forall m, In m ms -> ~ is_append_entries (snd m)).
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Lemma no_entries_past_current_term_timeout : raft_net_invariant_timeout no_entries_past_current_term.
Proof using.
unfold raft_net_invariant_timeout, no_entries_past_current_term.
intros.
find_apply_lem_hyp handleTimeout_spec.
intuition.
-
unfold no_entries_past_current_term_host in *.
intros.
simpl in *.
find_higher_order_rewrite; break_if; eauto.
subst; repeat find_rewrite.
eapply le_trans; [|eauto]; eauto.
-
Admitted.

Lemma handleAppendEntries_spec : forall h st t n pli plt es ci st' m, handleAppendEntries h st t n pli plt es ci = (st', m) -> (currentTerm st <= currentTerm st' /\ (forall e, In e (log st') -> In e (log st) \/ In e es /\ currentTerm st' = t) /\ ~ is_append_entries m).
Proof using.
intros.
unfold handleAppendEntries, advanceCurrentTerm in *.
Admitted.

Theorem no_entries_past_current_term_nw_not_append_entries : forall net ps' p' st', no_entries_past_current_term_nw net -> (forall p, In p ps' -> In p (nwPackets net) \/ p = p') -> ~ is_append_entries (pBody p') -> no_entries_past_current_term_nw (mkNetwork ps' st').
Proof using.
intros.
unfold no_entries_past_current_term_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
-
unfold no_entries_past_current_term_nw in *.
eauto.
-
subst.
exfalso.
match goal with H : _ |- _ => apply H end.
repeat eexists; eauto.
