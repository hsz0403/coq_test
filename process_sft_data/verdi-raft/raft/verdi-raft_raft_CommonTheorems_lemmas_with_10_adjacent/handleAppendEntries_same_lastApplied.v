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

Lemma wonElection_length : forall l1 l2, wonElection l1 = true -> length l1 <= length l2 -> wonElection l2 = true.
Proof using.
intros.
unfold wonElection in *.
do_bool.
Admitted.

Lemma wonElection_no_dup_in : forall l1 l2, wonElection l1 = true -> NoDup l1 -> (forall x, In x l1 -> In x l2) -> wonElection l2 = true.
Proof using.
intros.
Admitted.

Lemma wonElection_exists_voter : forall l, wonElection l = true -> exists x, In x l.
Proof using.
unfold wonElection.
intros.
destruct l; try discriminate.
simpl.
Admitted.

Lemma argmax_fun_ext : forall A (f : A -> nat) g l, (forall a, f a = g a) -> argmax f l = argmax g l.
Proof using.
intros.
induction l; simpl in *; intuition.
find_rewrite.
break_match; intuition.
repeat find_higher_order_rewrite.
Admitted.

Lemma argmax_None : forall A (f : A -> nat) l, argmax f l = None -> l = [].
Proof using.
intros.
destruct l; simpl in *; intuition.
Admitted.

Lemma argmax_elim : forall A (f : A -> nat) l a, argmax f l = Some a -> (In a l /\ forall x, In x l -> f a >= f x).
Proof using.
induction l; intros; simpl in *; [congruence|].
repeat break_match; find_inversion.
-
do_bool.
match goal with | H : forall _, Some ?a = Some _ -> _ |- _ => specialize (H a) end.
intuition; subst; auto.
find_apply_hyp_hyp.
omega.
-
do_bool.
match goal with | H : forall _, Some ?a = Some _ -> _ |- _ => specialize (H a) end.
intuition; subst; auto.
find_apply_hyp_hyp.
omega.
-
intuition; subst; auto.
find_apply_lem_hyp argmax_None.
subst.
Admitted.

Lemma argmax_in : forall A (f : A -> nat) l a, argmax f l = Some a -> In a l.
Proof using.
intros.
find_apply_lem_hyp argmax_elim.
Admitted.

Lemma argmax_one_different : forall A (A_eq_dec : forall x y : A, {x = y} + {x <> y}) f g (l : list A) a, (forall x, In x l -> a <> x -> f x = g x) -> (forall x, In x l -> f x <= g x) -> (argmax g l = argmax f l \/ argmax g l = Some a).
Proof using.
intros.
induction l; simpl in *; intuition.
conclude IHl intuition.
conclude IHl intuition.
intuition.
-
find_rewrite.
break_match; intuition.
repeat break_if; intuition.
+
do_bool.
right.
find_apply_lem_hyp argmax_in; intuition.
destruct (A_eq_dec a a1); destruct (A_eq_dec a a0); repeat subst; intuition; specialize (H0 a1); specialize (H a0); intuition; repeat find_rewrite; omega.
+
do_bool.
right.
find_apply_lem_hyp argmax_in; intuition.
destruct (A_eq_dec a a1); destruct (A_eq_dec a a0); repeat subst; intuition.
*
specialize (H a1); specialize (H0 a0); intuition.
repeat find_rewrite.
omega.
*
specialize (H a1); specialize (H0 a0); intuition.
repeat find_rewrite.
omega.
-
find_rewrite.
repeat break_match; subst; intuition.
do_bool.
repeat find_apply_lem_hyp argmax_elim; intuition.
destruct (A_eq_dec a a1); destruct (A_eq_dec a a0); repeat subst; intuition.
+
specialize (H a0); specialize (H0 a1); intuition.
repeat find_rewrite.
omega.
+
pose proof H a0; pose proof H a1; intuition.
repeat find_rewrite.
specialize (H3 a1).
intuition.
Admitted.

Lemma argmin_fun_ext : forall A (f : A -> nat) g l, (forall a, f a = g a) -> argmin f l = argmin g l.
Proof using.
intros.
induction l; simpl in *; intuition.
find_rewrite.
break_match; intuition.
repeat find_higher_order_rewrite.
Admitted.

Lemma argmin_None : forall A (f : A -> nat) l, argmin f l = None -> l = [].
Proof using.
intros.
destruct l; simpl in *; intuition.
Admitted.

Lemma handleAppendEntries_same_lastApplied : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> lastApplied st' = lastApplied st.
Proof using.
intros.
unfold handleAppendEntries in *.
repeat (break_match; repeat (find_inversion; simpl in *)); auto using advanceCurrentTerm_same_lastApplied.
