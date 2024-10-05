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

Lemma thing2 : forall l l' i, l <> [] -> Prefix l l' -> sorted l' -> contiguous_range_exact_lo l i -> contiguous_range_exact_lo l' 0 -> l ++ (removeAfterIndex l' i) = l'.
Proof using one_node_params.
induction l; try congruence; intros.
destruct l'; simpl.
-
contradiction.
-
simpl Prefix in *.
intuition.
subst a.
f_equal.
break_if.
+
do_bool.
unfold contiguous_range_exact_lo in *.
intuition.
simpl maxIndex in *.
specialize (H6 e).
specialize (H4 e).
assert (H_in': In e (e :: l')).
left.
reflexivity.
concludes.
assert (H_in: In e (e :: l)).
left.
reflexivity.
concludes.
omega.
+
destruct l.
{
do_bool.
simpl in *.
find_apply_lem_hyp contiguous_index_singleton.
destruct l'.
-
reflexivity.
-
simpl.
intuition.
specialize (H0 e0).
assert (H_in: In e0 (e0 :: l')).
left.
reflexivity.
concludes.
intuition.
find_rewrite.
break_if.
+
reflexivity.
+
do_bool.
omega.
}
{
apply IHl; try discriminate; auto.
-
find_apply_lem_hyp cons_contiguous_sorted.
+
firstorder.
+
eauto using Prefix_cons, prefix_sorted.
-
find_apply_lem_hyp cons_contiguous_sorted.
+
unfold contiguous_range_exact_lo in *.
inversion H1.
split; intros.
*
do_bool.
simpl maxIndex in *.
destruct H2.
destruct H3.
destruct l'; simpl in *; intuition.
subst_max.
specialize (H2 i0).
specialize (H0 e1).
conclude_using eauto.
break_and.
assert (i < i0 <= eIndex e) by omega.
concludes.
break_exists.
break_and.
subst.
exists x.
split; auto.
break_or_hyp; auto.
omega.
*
apply H2.
right; auto.
+
eauto using Prefix_cons, prefix_sorted.
-
apply cons_contiguous_sorted in H3; auto.
}
