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

Lemma no_entries_past_current_term_unaffected : forall net st' ps' xs p ys d ms, nwPackets net = xs ++ p :: ys -> no_entries_past_current_term net -> (forall h : Net.name, st' h = update name_eq_dec (nwState net) (pDst p) d h) -> (forall p' : packet, In p' ps' -> In p' (xs ++ ys) \/ In p' (send_packets (pDst p) ms)) -> currentTerm (nwState net (pDst p)) <= currentTerm d -> log d = log (nwState net (pDst p)) -> (forall m, In m ms -> ~ is_append_entries (snd m)) -> no_entries_past_current_term {| nwPackets := ps'; nwState := st' |}.
Proof using.
intros.
unfold no_entries_past_current_term in *.
intuition.
-
unfold no_entries_past_current_term_host in *.
intros.
simpl in *.
find_higher_order_rewrite.
break_if; eauto.
subst.
repeat find_rewrite.
eapply le_trans; [|eauto].
eauto.
-
unfold no_entries_past_current_term_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
+
intros.
match goal with | _ : In ?p _ |- _ => assert (In p (nwPackets net)) by (find_rewrite; in_crush) end.
eapply_prop no_entries_past_current_term_nw; eauto.
+
exfalso.
do_in_map.
subst.
simpl in *.
find_apply_hyp_hyp.
find_rewrite.
Admitted.

Lemma no_entries_past_current_term_unaffected_1 : forall net st' ps' xs p ys d m, nwPackets net = xs ++ p :: ys -> no_entries_past_current_term net -> (forall h : Net.name, st' h = update name_eq_dec (nwState net) (pDst p) d h) -> (forall p' : packet, In p' ps' -> In p' (xs ++ ys) \/ p' = m) -> currentTerm (nwState net (pDst p)) <= currentTerm d -> log d = log (nwState net (pDst p)) -> ~ is_append_entries (pBody m) -> no_entries_past_current_term {| nwPackets := ps'; nwState := st' |}.
Proof using.
intros.
unfold no_entries_past_current_term in *.
intuition.
-
unfold no_entries_past_current_term_host in *.
intros.
simpl in *.
find_higher_order_rewrite.
break_if; eauto.
subst.
repeat find_rewrite.
eapply le_trans; [|eauto].
eauto.
-
unfold no_entries_past_current_term_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
+
intros.
match goal with | _ : In ?p _ |- _ => assert (In p (nwPackets net)) by (find_rewrite; in_crush) end.
eapply_prop no_entries_past_current_term_nw; eauto.
+
exfalso.
subst.
repeat find_rewrite.
forwards; intuition.
Admitted.

Lemma no_entries_past_current_term_unaffected_0 : forall net st' ps' xs p ys d, nwPackets net = xs ++ p :: ys -> no_entries_past_current_term net -> (forall h : Net.name, st' h = update name_eq_dec (nwState net) (pDst p) d h) -> (forall p' : packet, In p' ps' -> In p' (xs ++ ys)) -> currentTerm (nwState net (pDst p)) <= currentTerm d -> log d = log (nwState net (pDst p)) -> no_entries_past_current_term {| nwPackets := ps'; nwState := st' |}.
Proof using.
intros.
unfold no_entries_past_current_term in *.
intuition.
-
unfold no_entries_past_current_term_host in *.
intros.
simpl in *.
find_higher_order_rewrite.
break_if; eauto.
subst.
repeat find_rewrite.
eapply le_trans; [|eauto].
eauto.
-
unfold no_entries_past_current_term_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
match goal with | _ : In ?p _ |- _ => assert (In p (nwPackets net)) by (find_rewrite; in_crush) end.
Admitted.

Lemma handleAppendEntriesReply_spec : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> (currentTerm st <= currentTerm st' /\ log st' = log st /\ (forall m, In m ms -> ~ is_append_entries (snd m))).
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
Admitted.

Lemma no_entries_past_current_term_append_entries_reply : raft_net_invariant_append_entries_reply no_entries_past_current_term.
Proof using.
unfold raft_net_invariant_append_entries_reply.
intros.
find_apply_lem_hyp handleAppendEntriesReply_spec.
Admitted.

Lemma handleRequestVote_spec : forall h st t h' pli plt st' m, handleRequestVote h st t h' pli plt = (st', m) -> (currentTerm st <= currentTerm st' /\ log st' = log st /\ ~ is_append_entries m).
Proof using.
intros.
unfold handleRequestVote, advanceCurrentTerm in *.
Admitted.

Lemma no_entries_past_current_term_request_vote : raft_net_invariant_request_vote no_entries_past_current_term.
Proof using.
unfold raft_net_invariant_request_vote.
intros.
find_apply_lem_hyp handleRequestVote_spec.
Admitted.

Lemma handleRequestVoteReply_spec : forall h st h' t v st', handleRequestVoteReply h st h' t v = st' -> (currentTerm st <= currentTerm st' /\ log st' = log st).
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
Admitted.

Lemma no_entries_past_current_term_request_vote_reply : raft_net_invariant_request_vote_reply no_entries_past_current_term.
Proof using.
unfold raft_net_invariant_request_vote_reply.
intros.
find_apply_lem_hyp handleRequestVoteReply_spec.
Admitted.

Lemma no_entries_past_current_term_state_same_packet_subset : raft_net_invariant_state_same_packet_subset no_entries_past_current_term.
Proof using.
unfold raft_net_invariant_state_same_packet_subset, no_entries_past_current_term, no_entries_past_current_term_host, no_entries_past_current_term_nw.
intros.
intuition.
-
repeat find_reverse_higher_order_rewrite.
eauto.
-
find_apply_hyp_hyp.
Admitted.

Theorem no_entries_past_current_term_invariant : forall net, raft_intermediate_reachable net -> no_entries_past_current_term net.
Proof using.
intros.
eapply raft_net_invariant; eauto.
-
apply no_entries_past_current_term_init.
-
apply no_entries_past_current_term_client_request.
-
apply no_entries_past_current_term_timeout.
-
apply no_entries_past_current_term_append_entries.
-
apply no_entries_past_current_term_append_entries_reply.
-
apply no_entries_past_current_term_request_vote.
-
apply no_entries_past_current_term_request_vote_reply.
-
apply no_entries_past_current_term_do_leader.
-
apply no_entries_past_current_term_do_generic_server.
-
apply no_entries_past_current_term_state_same_packet_subset.
-
Admitted.

Instance tsi : term_sanity_interface.
Proof.
split.
Admitted.

Lemma no_entries_past_current_term_reboot : raft_net_invariant_reboot no_entries_past_current_term.
Proof using.
unfold raft_net_invariant_reboot, no_entries_past_current_term, no_entries_past_current_term_host, no_entries_past_current_term_nw, reboot.
intuition.
-
repeat find_higher_order_rewrite.
simpl in *.
subst.
break_if; simpl in *; intuition.
-
find_reverse_rewrite.
eauto.
