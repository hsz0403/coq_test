Require Import PeanoNat.
Require Import VerdiRaft.RaftState.
Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Export VerdiRaft.CommonDefinitions.
Require Import FunInd.
Section CommonTheorems.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Notation disjoint xs ys := (forall x, In x xs -> In x ys -> False).
Definition contiguous_range_exact_lo xs lo := (forall i, lo < i <= maxIndex xs -> exists e, eIndex e = i /\ In e xs) /\ (forall e, In e xs -> lo < eIndex e).
Definition entries_match' entries entries' := forall e e' e'', eIndex e = eIndex e' -> eTerm e = eTerm e' -> In e entries -> In e' entries' -> eIndex e'' <= eIndex e -> (In e'' entries -> In e'' entries').
Definition contiguous (prevLogIndex : logIndex) (prevLogTerm : term) (leaderLog entries : list entry) : Prop := (prevLogIndex = 0 \/ exists e, findAtIndex leaderLog prevLogIndex = Some e /\ eTerm e = prevLogTerm) /\ (forall e, In e leaderLog -> eIndex e > prevLogIndex -> eIndex e <= maxIndex entries -> In e entries) /\ forall e e', eIndex e = eIndex e' -> eTerm e = eTerm e' -> In e entries -> In e' leaderLog -> e = e'.
Definition term_of (m : msg) := match m with | RequestVote t _ _ _ => Some t | RequestVoteReply t _ => Some t | AppendEntries t _ _ _ _ _ => Some t | AppendEntriesReply t _ _ => Some t end.
Ltac use_entries_match := match goal with | [ _ : eIndex ?e1 = eIndex ?e2, H : context [entries_match] |- _ ] => first [ solve [eapply H with (e:=e2)(e':=e1); eauto; congruence] | solve [eapply H with (e:=e1)(e':=e2); eauto; congruence]] end.
Functional Scheme div2_ind := Induction for div2 Sort Prop.
End CommonTheorems.
Notation is_append_entries m := (exists t n prevT prevI entries c, m = AppendEntries t n prevT prevI entries c).
Notation is_request_vote_reply m := (exists t r, m = RequestVoteReply t r).
Ltac use_applyEntries_spec := match goal with | H : context [applyEntries] |- _ => eapply applyEntries_spec in H; eauto; break_exists end.
Ltac unfold_invariant hyp := (red in hyp; (* try unfolding the invariant and look for conjunction *) match type of hyp with | _ /\ _ => break_and | _ => fail 1 (* better to not unfold *) end) || break_and.
Ltac intro_invariant lem := match goal with | [ h: raft_intermediate_reachable _ |- _ ] => let x := fresh in pose proof h as x; apply lem in x; unfold_invariant x end.

Lemma entries_match_sym : forall xs ys, entries_match xs ys -> entries_match ys xs.
Proof using.
intros.
unfold entries_match in *.
intros.
intuition.
-
apply H with (e:=e')(e':=e); auto.
repeat find_rewrite.
auto.
-
apply H with (e:=e')(e':=e); auto.
repeat find_rewrite.
Admitted.

Lemma advanceCurrentTerm_same_log : forall st t, log (advanceCurrentTerm st t) = log st.
Proof using.
unfold advanceCurrentTerm.
intros.
Admitted.

Lemma tryToBecomeLeader_same_log : forall n st out st' ms, tryToBecomeLeader n st = (out, st', ms) -> log st' = log st.
Proof using.
unfold tryToBecomeLeader.
intros.
find_inversion.
Admitted.

Lemma handleRequestVote_same_log : forall n st t c li lt st' ms, handleRequestVote n st t c li lt = (st', ms) -> log st' = log st.
Proof using.
unfold handleRequestVote.
intros.
Admitted.

Lemma handleRequestVoteReply_same_log : forall n st src t v, log (handleRequestVoteReply n st src t v) = log st.
Proof using.
unfold handleRequestVoteReply.
intros.
Admitted.

Lemma advanceCurrentTerm_same_lastApplied : forall st t, lastApplied (advanceCurrentTerm st t) = lastApplied st.
Proof using.
unfold advanceCurrentTerm.
intros.
Admitted.

Theorem handleTimeout_lastApplied : forall h st out st' ps, handleTimeout h st = (out, st', ps) -> lastApplied st' = lastApplied st.
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *.
Admitted.

Theorem handleClientRequest_lastApplied: forall h st client id c out st' ps, handleClientRequest h st client id c = (out, st', ps) -> lastApplied st' = lastApplied st.
Proof using.
intros.
unfold handleClientRequest in *.
Admitted.

Lemma tryToBecomeLeader_same_lastApplied : forall n st out st' ms, tryToBecomeLeader n st = (out, st', ms) -> lastApplied st' = lastApplied st.
Proof using.
unfold tryToBecomeLeader.
intros.
find_inversion.
Admitted.

Lemma handleRequestVote_same_lastApplied : forall n st t c li lt st' ms, handleRequestVote n st t c li lt = (st', ms) -> lastApplied st' = lastApplied st.
Proof using.
unfold handleRequestVote.
intros.
Admitted.

Lemma findAtIndex_elim : forall l i e, findAtIndex l i = Some e -> i = eIndex e /\ In e l.
Proof using.
Admitted.

Lemma index_in_bounds : forall e es i, sorted es -> In e es -> i <> 0 -> i <= eIndex e -> 1 <= i <= maxIndex es.
Proof using.
intros.
split.
-
omega.
-
etransitivity; eauto.
Admitted.

Lemma rachet : forall x x' xs ys, eIndex x = eIndex x' -> In x xs -> In x' ys -> In x' xs -> uniqueIndices xs -> In x ys.
Proof using.
intros.
assert (x = x').
-
eapply uniqueIndices_elim_eq; eauto.
-
subst.
Admitted.

Lemma findAtIndex_intro : forall l i e, sorted l -> In e l -> eIndex e = i -> uniqueIndices l -> findAtIndex l i = Some e.
Proof using.
induction l; intros.
-
simpl in *.
intuition.
-
simpl in *.
intuition; break_if; subst; do_bool.
+
auto.
+
congruence.
+
f_equal.
eauto using uniqueIndices_elim_eq with *.
+
break_if; eauto.
*
do_bool.
find_apply_hyp_hyp.
omega.
*
eapply IHl; auto.
unfold uniqueIndices in *.
simpl in *.
Admitted.

Theorem sorted_uniqueIndices : forall l, sorted l -> uniqueIndices l.
Proof using.
intros; induction l; simpl; auto.
-
unfold uniqueIndices.
simpl.
constructor.
-
unfold uniqueIndices in *.
simpl in *.
intuition.
constructor; eauto.
intuition.
do_in_map.
find_apply_hyp_hyp.
Admitted.

Lemma findAtIndex_intro' : forall l i e, sorted l -> In e l -> eIndex e = i -> findAtIndex l i = Some e.
Proof using.
intros.
Admitted.

Lemma doLeader_same_log : forall st n os st' ms, doLeader st n = (os, st', ms) -> log st' = log st.
Proof using.
unfold doLeader.
intros.
Admitted.

Lemma handleAppendEntriesReply_same_log : forall n st src t es b st' l, handleAppendEntriesReply n st src t es b = (st', l) -> log st' = log st.
Proof using.
intros.
unfold handleAppendEntriesReply in *.
Admitted.

Lemma handleAppendEntriesReply_same_lastApplied : forall n st src t es b st' l, handleAppendEntriesReply n st src t es b = (st', l) -> lastApplied st' = lastApplied st.
Proof using.
intros.
unfold handleAppendEntriesReply in *.
Admitted.

Lemma handleAppendEntries_same_lastApplied : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> lastApplied st' = lastApplied st.
Proof using.
intros.
unfold handleAppendEntries in *.
Admitted.

Lemma handleRequestVoteReply_same_lastApplied : forall n st src t v, lastApplied (handleRequestVoteReply n st src t v) = lastApplied st.
Proof using.
unfold handleRequestVoteReply.
intros.
repeat break_match; simpl; auto using advanceCurrentTerm_same_lastApplied.
