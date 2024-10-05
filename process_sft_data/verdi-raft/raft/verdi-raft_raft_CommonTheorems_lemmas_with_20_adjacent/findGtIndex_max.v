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

Lemma removeAfterIndex_2_subseq : forall xs i j, subseq (removeAfterIndex (removeAfterIndex xs i) j) (removeAfterIndex (removeAfterIndex xs j) i).
Proof using.
induction xs; intros; simpl.
-
auto.
-
repeat (break_match; simpl); intuition; try discriminate.
+
eauto using subseq_refl.
+
do_bool.
assert (j < i) by omega.
rewrite removeAfterIndex_le with (j := i) (i := j) at 1; auto; omega.
+
do_bool.
assert (i < j) by omega.
Admitted.

Lemma removeAfterIndex_comm : forall xs i j, removeAfterIndex (removeAfterIndex xs i) j = removeAfterIndex (removeAfterIndex xs j) i.
Proof using.
Admitted.

Lemma removeAfterIndex_2_eq_min : forall xs i j, removeAfterIndex (removeAfterIndex xs i) j = removeAfterIndex xs (min i j).
Proof using.
intros.
pose proof Min.min_spec i j.
intuition.
-
find_rewrite.
rewrite removeAfterIndex_le with (i := i) (j := j) at 2; eauto using removeAfterIndex_comm; omega.
-
find_rewrite.
Admitted.

Lemma findAtIndex_None : forall xs i x, sorted xs -> findAtIndex xs i = None -> In x xs -> eIndex x <> i.
Proof using.
induction xs; intros; simpl in *; intuition; break_match; try discriminate.
-
subst.
do_bool.
congruence.
-
do_bool.
break_if; eauto.
do_bool.
find_apply_hyp_hyp.
Admitted.

Lemma findAtIndex_removeAfterIndex_agree : forall xs i j e e', NoDup (map eIndex xs) -> findAtIndex xs i = Some e -> findAtIndex (removeAfterIndex xs j) i = Some e' -> e = e'.
Proof using.
intros.
eapply NoDup_map_elim with (f := eIndex); eauto using findAtIndex_in, removeAfterIndex_in.
apply findAtIndex_index in H0.
apply findAtIndex_index in H1.
Admitted.

Lemma subseq_uniqueIndices : forall ys xs, subseq xs ys -> uniqueIndices ys -> uniqueIndices xs.
Proof using.
unfold uniqueIndices.
induction ys; intros.
-
simpl in *.
break_match; intuition.
-
simpl in *.
break_match; intuition.
+
simpl.
constructor.
+
subst.
simpl in *.
invc H0.
constructor; auto.
intro.
apply H3.
eapply subseq_In; eauto.
apply subseq_map.
auto.
+
subst.
invc H0.
Admitted.

Lemma subseq_findGtIndex : forall xs i, subseq (findGtIndex xs i) xs.
Proof using.
induction xs; intros.
-
simpl.
auto.
-
simpl.
repeat break_match; auto.
+
find_inversion.
eauto.
+
Admitted.

Lemma findGtIndex_in : forall xs i x, In x (findGtIndex xs i) -> In x xs.
Proof using.
Admitted.

Lemma findGtIndex_sufficient : forall e entries x, sorted entries -> In e entries -> eIndex e > x -> In e (findGtIndex entries x).
Proof using.
induction entries; intros.
-
simpl in *.
intuition.
-
simpl in *.
break_if; intuition.
+
subst.
in_crush.
+
subst.
do_bool.
omega.
+
do_bool.
find_apply_hyp_hyp.
Admitted.

Lemma removeAfterIndex_uniqueIndices : forall l i, uniqueIndices l -> uniqueIndices (removeAfterIndex l i).
Proof with eauto using subseq_uniqueIndices, removeAfterIndex_subseq.
Admitted.

Lemma maxIndex_subset : forall xs ys, sorted xs -> sorted ys -> (forall x, In x xs -> In x ys) -> maxIndex xs <= maxIndex (orig_base_params:=orig_base_params) ys.
Proof using.
destruct xs; intros.
-
simpl.
omega.
-
destruct ys; simpl in *.
+
match goal with | [ H : forall _, _ = _ \/ _ -> _, a : entry |- _ ] => solve [ specialize (H a); intuition ] end.
+
match goal with | [ H : forall _, _ = _ \/ _ -> _ |- eIndex ?a <= _ ] => specialize (H a); intuition end; subst; auto.
find_apply_hyp_hyp.
Admitted.

Lemma maxIndex_exists_in : forall xs, maxIndex xs >= 1 -> exists x, eIndex x = maxIndex xs /\ In x xs.
Proof using.
destruct xs; intros.
-
simpl in *.
omega.
-
simpl in *.
Admitted.

Lemma maxIndex_app : forall l l', maxIndex (l ++ l') = maxIndex l \/ maxIndex (l ++ l') = maxIndex l' /\ l = [].
Proof using.
Admitted.

Lemma maxIndex_removeAfterIndex_le : forall l i, sorted l -> maxIndex (removeAfterIndex l i) <= maxIndex l.
Proof using.
intros.
apply maxIndex_subset; eauto using removeAfterIndex_sorted.
intros.
Admitted.

Lemma maxIndex_removeAfterIndex : forall l i e, sorted l -> In e l -> eIndex e = i -> maxIndex (removeAfterIndex l i) = i.
Proof using.
induction l; intros; simpl in *; intuition.
-
subst.
break_if; do_bool; try omega.
reflexivity.
-
break_if; simpl in *.
+
do_bool.
match goal with | H : forall _, In _ _ -> _ |- _ => specialize (H2 e) end.
intuition.
omega.
+
Admitted.

Lemma maxIndex_gt_0_nonempty : forall es, 0 < maxIndex es -> es <> nil.
Proof using.
intros.
destruct es; simpl in *.
-
omega.
-
Admitted.

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

Lemma findGtIndex_max : forall entries x, maxIndex (findGtIndex entries x) <= maxIndex entries.
Proof using.
intros.
destruct entries; simpl; auto.
break_if; simpl; intuition.
