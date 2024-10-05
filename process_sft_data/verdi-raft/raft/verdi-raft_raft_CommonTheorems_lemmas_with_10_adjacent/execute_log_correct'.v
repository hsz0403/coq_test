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

Lemma handleAppendEntriesReply_same_commitIndex : forall n st src t es b st' l, handleAppendEntriesReply n st src t es b = (st', l) -> commitIndex st' = commitIndex st.
Proof using.
unfold handleAppendEntriesReply, advanceCurrentTerm.
intros.
Admitted.

Lemma handleRequestVote_same_commitIndex : forall n st t c li lt st' ms, handleRequestVote n st t c li lt = (st', ms) -> commitIndex st' = commitIndex st.
Proof using.
unfold handleRequestVote, advanceCurrentTerm.
intros.
Admitted.

Lemma handleRequestVoteReply_same_commitIndex : forall n st src t v, commitIndex (handleRequestVoteReply n st src t v) = commitIndex st.
Proof using.
unfold handleRequestVoteReply, advanceCurrentTerm.
intros.
Admitted.

Lemma doGenericServer_commitIndex : forall h st out st' ms, doGenericServer h st = (out, st', ms) -> commitIndex st' = commitIndex st.
Proof using.
unfold doGenericServer.
intros.
Admitted.

Theorem div2_correct' : forall n, n <= div2 n + S (div2 n).
Proof using.
intro n.
Admitted.

Theorem div2_correct : forall c a b, a > div2 c -> b > div2 c -> a + b > c.
Proof using.
intros n.
functional induction (div2 n); intros; try omega.
specialize (IHn0 (pred a) (pred b)).
Admitted.

Lemma wonElection_one_in_common : forall l l', wonElection (dedup name_eq_dec l) = true -> wonElection (dedup name_eq_dec l') = true -> exists h, In h l /\ In h l'.
Proof using.
intros.
unfold wonElection in *.
do_bool.
cut (exists h, In h (dedup name_eq_dec l) /\ In h (dedup name_eq_dec l')); [intros; break_exists; exists x; intuition eauto using in_dedup_was_in|].
Admitted.

Lemma execute_log'_app : forall xs ys st tr, execute_log' (xs ++ ys) st tr = let (tr', st') := execute_log' xs st tr in execute_log' ys st' tr'.
Proof using.
induction xs; intros.
-
auto.
-
simpl in *.
repeat break_let.
rewrite IHxs.
break_let.
find_inversion.
Admitted.

Lemma fst_execute_log' : forall log st tr, fst (execute_log' log st tr) = tr ++ fst (execute_log' log st []).
Proof using.
induction log; intros.
-
simpl.
rewrite app_nil_r.
auto.
-
simpl.
break_let.
rewrite IHlog.
rewrite app_ass.
simpl.
rewrite IHlog with (tr := [(eInput a, o)]).
Admitted.

Lemma snd_execute_log' : forall log st tr, snd (execute_log' log st tr) = snd (execute_log' log st []).
Proof using.
induction log; intros.
-
auto.
-
simpl.
break_let.
rewrite IHlog.
rewrite IHlog with (tr := [(eInput a, o)]).
Admitted.

Lemma execute_log_correct : forall log, step_1_star init (snd (execute_log log)) (fst (execute_log log)).
Proof using.
intros.
Admitted.

Lemma contiguous_nil : forall i, contiguous_range_exact_lo [] i.
Proof using.
unfold contiguous_range_exact_lo.
intuition.
-
simpl in *.
omega.
-
Admitted.

Lemma contiguous_index_singleton : forall i a, contiguous_range_exact_lo [a] i -> eIndex a = S i.
Proof using.
intros.
unfold contiguous_range_exact_lo in *.
intuition.
specialize (H1 a).
specialize (H0 (S i)).
assert (H_a: In a [a]) by auto with datatypes.
concludes.
assert (H_s: i < S i) by auto.
concludes.
break_exists.
break_and.
inversion H0; subst; auto.
Admitted.

Lemma contiguous_index_adjacent : forall l i a b, sorted (a :: b :: l) -> contiguous_range_exact_lo (a :: b :: l) i -> eIndex a = S (eIndex b) /\ eIndex a > i.
Proof using.
intros.
unfold contiguous_range_exact_lo in *.
intuition.
assert (i < S (eIndex b) <= eIndex a).
simpl in *.
intuition.
specialize (H0 b).
concludes.
intuition.
specialize (H1 (S (eIndex b))).
concludes.
break_exists.
simpl In in *.
intuition; subst.
-
auto.
-
omega.
-
simpl in *.
intuition.
specialize (H x).
concludes.
Admitted.

Lemma cons_contiguous_sorted : forall l i a, sorted (a :: l) -> contiguous_range_exact_lo (a :: l) i -> contiguous_range_exact_lo l i.
Proof using.
induction l; intros.
-
apply contiguous_nil.
-
eapply contiguous_index_adjacent in H; eauto.
unfold contiguous_range_exact_lo in *.
break_and.
intuition.
simpl maxIndex in *.
specialize (H0 i0).
assert (i < i0 <= eIndex a0) by omega.
concludes.
break_exists.
intuition.
simpl in *.
intuition; subst.
+
omega.
+
exists x.
intuition.
+
exists x.
Admitted.

Lemma contiguous_app : forall l1 l2 i, sorted (l1 ++ l2) -> contiguous_range_exact_lo (l1 ++ l2) i -> contiguous_range_exact_lo l2 i.
Proof using.
induction l1; intros.
-
auto.
-
simpl ((a :: l1) ++ l2) in *.
find_apply_lem_hyp cons_contiguous_sorted; auto.
simpl in *.
Admitted.

Lemma prefix_sorted : forall l l', sorted l -> Prefix l' l -> sorted l'.
Proof using.
induction l; intros.
-
find_apply_lem_hyp Prefix_nil.
subst.
auto.
-
destruct l'.
+
auto.
+
simpl.
split.
*
intros.
simpl in *.
break_and.
find_eapply_lem_hyp Prefix_in; eauto.
find_insterU.
econcludes.
subst.
intuition.
*
Admitted.

Lemma prefix_contiguous : forall l l' e i, l' <> [] -> Prefix l' l -> sorted l -> In e l -> eIndex e > i -> contiguous_range_exact_lo l' i -> In e l'.
Proof using.
induction l; intros.
-
contradiction.
-
destruct l'; try congruence.
find_copy_apply_lem_hyp prefix_sorted; auto.
simpl in *.
intuition.
+
left.
subst.
reflexivity.
+
right.
subst.
destruct l'.
*
find_apply_lem_hyp contiguous_index_singleton.
specialize (H0 e).
concludes.
omega.
*
eapply IHl; try discriminate; eauto.
eapply cons_contiguous_sorted; eauto.
simpl in *.
Admitted.

Lemma removeAfterIndex_contiguous : forall l i i', sorted l -> contiguous_range_exact_lo l i -> contiguous_range_exact_lo (removeAfterIndex l i') i.
Proof using.
induction l; intros; simpl in *; intuition.
break_if; auto.
do_bool.
eapply IHl; eauto.
eapply cons_contiguous_sorted; eauto.
Admitted.

Lemma sorted_NoDup : forall l, sorted l -> NoDup l.
Proof using.
induction l; intros; simpl in *; auto.
-
constructor.
-
constructor; intuition.
match goal with | H : forall _, _ |- _ => specialize (H a) end.
Admitted.

Lemma execute_log_correct' : forall log st, step_1_star st (snd (execute_log' log st [])) (fst (execute_log' log st [])).
Proof using.
induction log; intros.
-
simpl.
constructor.
-
simpl.
break_let.
rewrite fst_execute_log'.
rewrite snd_execute_log'.
unfold step_1_star in *.
econstructor.
+
constructor.
eauto.
+
auto.
