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

Lemma sorted_NoDup : forall l, sorted l -> NoDup l.
Proof using.
induction l; intros; simpl in *; auto.
-
constructor.
-
constructor; intuition.
match goal with | H : forall _, _ |- _ => specialize (H a) end.
Admitted.

Lemma sorted_Permutation_eq : forall l l', sorted l -> sorted l' -> Permutation l l' -> l = l'.
Proof using.
induction l; intros.
-
symmetry.
apply Permutation_nil.
assumption.
-
destruct l'.
+
apply Permutation_nil.
apply Permutation_sym.
assumption.
+
simpl in *.
intuition.
find_copy_eapply_lem_hyp Permutation_in; intuition.
find_copy_apply_lem_hyp Permutation_sym.
find_copy_eapply_lem_hyp Permutation_in; intuition.
simpl in *.
intuition; try (subst a; f_equal; eauto using Permutation_cons_inv).
repeat find_apply_hyp_hyp.
intuition.
Admitted.

Lemma removeAfterIndex_same_sufficient : forall x l l', sorted l -> sorted l' -> (forall e, eIndex e <= x -> In e l -> In e l') -> (forall e, eIndex e <= x -> In e l' -> In e l) -> removeAfterIndex l' x = removeAfterIndex l x.
Proof using.
intros.
apply sorted_Permutation_eq; try (apply removeAfterIndex_sorted; assumption).
apply NoDup_Permutation; try (apply NoDup_removeAfterIndex; apply sorted_NoDup; assumption).
Admitted.

Lemma removeAfterIndex_same_sufficient' : forall x l l', sorted l -> sorted l' -> contiguous_range_exact_lo l 0 -> (forall e, In e l' -> 0 < eIndex e) -> x <= maxIndex l -> (forall e, eIndex e <= x -> In e l -> In e l') -> removeAfterIndex l' x = removeAfterIndex l x.
Proof using.
intros.
eapply removeAfterIndex_same_sufficient; eauto.
intros.
unfold contiguous_range_exact_lo in *.
intuition.
specialize (H7 (eIndex e)).
intuition.
find_copy_apply_hyp_hyp.
repeat conclude_using omega.
break_exists.
intuition.
symmetry in H9.
copy_apply H4 H10; try omega.
Admitted.

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
Admitted.

Lemma thing : forall es l l' e e', sorted l -> sorted l' -> contiguous_range_exact_lo l' 0 -> entries_match l l' -> es <> [] -> Prefix es l' -> contiguous_range_exact_lo es (eIndex e) -> In e l -> In e' l' -> eIndex e = eIndex e' -> eTerm e = eTerm e' -> es ++ (removeAfterIndex l (eIndex e)) = l'.
Proof using one_node_params.
intros.
rewrite removeAfterIndex_same_sufficient with (l := l'); auto.
-
apply thing2; auto.
-
unfold entries_match in *.
intros.
eapply H2; eauto.
-
unfold entries_match in *.
intros.
Admitted.

Lemma sorted_findGtIndex_0 : forall l, (forall e, In e l -> eIndex e > 0) -> sorted l -> findGtIndex l 0 = l.
Proof using.
induction l; intros; simpl in *; intuition.
break_if; intuition.
-
f_equal.
auto.
-
do_bool.
Admitted.

Lemma findGtIndex_app_in_1 : forall l1 l2 e, sorted (l1 ++ l2) -> In e l1 -> exists l', findGtIndex (l1 ++ l2) (eIndex e) = l' /\ forall x, In x l' -> In x l1.
Proof using.
induction l1; intros; simpl in *; intuition.
-
subst.
break_if; do_bool; try omega.
eexists; repeat (simpl in *; intuition).
-
specialize (H1 e); intuition.
conclude H1 ltac:(apply in_app_iff; intuition).
break_if; do_bool; try omega.
eexists; intuition; eauto.
simpl in *.
intuition.
eapply_prop_hyp sorted sorted; eauto.
break_exists; intuition.
find_rewrite.
Admitted.

Lemma sorted_app_in_1 : forall l1 l2 e, sorted (l1 ++ l2) -> eIndex e > 0 -> In e l1 -> eIndex e > maxIndex l2.
Proof using.
induction l1; intros; simpl in *; intuition.
subst.
destruct l2; simpl in *; auto.
Admitted.

Lemma findGtIndex_Prefix : forall l i, Prefix (findGtIndex l i) l.
Proof using.
induction l; intros; simpl in *; intuition.
Admitted.

Lemma removeAfterIndex_contiguous : forall l i i', sorted l -> contiguous_range_exact_lo l i -> contiguous_range_exact_lo (removeAfterIndex l i') i.
Proof using.
induction l; intros; simpl in *; intuition.
break_if; auto.
do_bool.
eapply IHl; eauto.
eapply cons_contiguous_sorted; eauto.
simpl; intuition.
