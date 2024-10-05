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

Lemma removeIncorrect_new_contiguous : forall new current prev e, sorted current -> uniqueIndices current -> (forall e e', eIndex e = eIndex e' -> eTerm e = eTerm e' -> In e new -> In e' current -> e = e') -> contiguous_range_exact_lo current 0 -> contiguous_range_exact_lo new prev -> In e current -> eIndex e = prev -> contiguous_range_exact_lo (new ++ removeAfterIndex current prev) 0.
Proof using one_node_params.
intros new current prev e Hsorted Huniq Hinv.
intros.
red.
intros.
intuition.
-
destruct (le_lt_dec i prev).
+
unfold contiguous_range_exact_lo in *.
intuition.
match goal with | H: forall _, _ < _ <= _ current -> _, H' : In _ current |- _ => specialize (H i); apply maxIndex_is_max in H'; auto; forward H; intuition end.
break_exists.
exists x.
intuition.
apply in_or_app.
right.
subst.
eapply removeAfterIndex_le_In; eauto.
+
pose proof maxIndex_app new (removeAfterIndex current prev).
intuition.
*
find_rewrite.
unfold contiguous_range_exact_lo in *.
intuition.
match goal with | H: forall _, _ < _ <= _ new -> _ |- _ => specialize (H i); auto; forward H; intuition end.
break_exists.
exists x.
intuition.
*
subst.
simpl in *.
clean.
exfalso.
pose proof maxIndex_removeAfterIndex current (eIndex e) e.
intuition.
-
unfold contiguous_range_exact_lo in *.
do_in_app.
intuition.
+
firstorder.
+
Admitted.

Lemma incoming_entries_in_log : forall es log x i, In x es -> uniqueIndices log -> exists y, eIndex x = eIndex y /\ eTerm x = eTerm y /\ In y (es ++ (removeAfterIndex log i)).
Proof using.
intros.
exists x.
Admitted.

Lemma findGtIndex_necessary : forall entries e x, In e (findGtIndex entries x) -> In e entries /\ eIndex e > x.
Proof using.
induction entries; intros; simpl in *; intuition.
-
break_if; simpl in *; intuition; right; eapply IHentries; eauto.
-
break_if; simpl in *; intuition.
+
do_bool.
subst.
omega.
+
Admitted.

Lemma findGtIndex_contiguous : forall entries x, sorted entries -> (forall i, 0 < i <= maxIndex entries -> (exists e, In e entries /\ eIndex e = i)) -> forall i, x < i <= maxIndex entries -> exists e, In e (findGtIndex entries x) /\ eIndex e = i.
Proof using.
intros entries x Hsorted; intros.
specialize (H i).
conclude H ltac:(omega).
break_exists.
exists x0.
intuition.
Admitted.

Lemma findGtIndex_max : forall entries x, maxIndex (findGtIndex entries x) <= maxIndex entries.
Proof using.
intros.
destruct entries; simpl; auto.
Admitted.

Lemma findAtIndex_uniq_equal : forall e e' es, findAtIndex es (eIndex e) = Some e' -> In e es -> uniqueIndices es -> e = e'.
Proof using.
intros.
pose proof findAtIndex_in _ _ _ H.
pose proof findAtIndex_index _ _ _ H.
Admitted.

Lemma entries_match_entries_match' : forall xs ys, entries_match xs ys -> entries_match' xs ys /\ entries_match' ys xs.
Proof using.
unfold entries_match, entries_match'.
intros.
intuition.
-
eapply H; eauto.
-
Admitted.

Lemma entries_match_refl : forall l, entries_match l l.
Proof using.
unfold entries_match.
Admitted.

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

Lemma handleRequestVoteReply_same_lastApplied : forall n st src t v, lastApplied (handleRequestVoteReply n st src t v) = lastApplied st.
Proof using.
unfold handleRequestVoteReply.
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

Lemma tryToBecomeLeader_same_log : forall n st out st' ms, tryToBecomeLeader n st = (out, st', ms) -> log st' = log st.
Proof using.
unfold tryToBecomeLeader.
intros.
find_inversion.
auto.
