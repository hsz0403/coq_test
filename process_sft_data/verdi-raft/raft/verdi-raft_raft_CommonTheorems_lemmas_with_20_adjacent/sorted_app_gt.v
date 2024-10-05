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

Lemma removeAfterIndex_in_app_l' : forall l l' e, (forall e', In e' l -> eIndex e' > eIndex e) -> In e l' -> removeAfterIndex (l ++ l') (eIndex e) = removeAfterIndex l' (eIndex e).
Proof using.
induction l; intros; simpl in *; intuition; subst; break_if; do_bool; eauto using app_ass.
specialize (H a).
intuition.
Admitted.

Lemma removeAfterIndex_maxIndex_sorted : forall l, sorted l -> l = removeAfterIndex l (maxIndex l).
Proof using.
intros; induction l; simpl in *; intuition.
break_if; auto.
do_bool.
Admitted.

Lemma contiguous_singleton_sufficient : forall x n, S n = eIndex x -> contiguous_range_exact_lo [x] n.
Proof using.
red.
intuition.
-
exists x.
intuition.
simpl in *.
inv H2; [reflexivity | omega].
-
simpl in *.
intuition.
subst.
Admitted.

Lemma contiguous_adjacent_sufficient : forall x y l i, eIndex x = S (eIndex y) -> contiguous_range_exact_lo (y :: l) i -> contiguous_range_exact_lo (x :: y :: l) i.
Proof using.
intros.
unfold contiguous_range_exact_lo in *.
intuition.
-
invc H4.
+
eexists; intuition.
+
find_rewrite.
find_apply_lem_hyp Nat.succ_inj.
subst.
assert (i < i0 <= maxIndex (y :: l)).
simpl.
omega.
find_apply_hyp_hyp.
break_exists.
simpl in *.
intuition; subst; eexists; intuition.
-
simpl in *.
intuition; subst; auto.
specialize (H2 y).
concludes.
Admitted.

Lemma contiguous_partition : forall l1 x l2 i, sorted (l1 ++ x :: l2) -> contiguous_range_exact_lo (l1 ++ x :: l2) i -> contiguous_range_exact_lo l1 (eIndex x).
Proof using.
Opaque sorted.
induction l1; intros.
-
apply contiguous_nil.
-
destruct l1; simpl in *; find_copy_apply_lem_hyp contiguous_index_adjacent; auto.
+
apply contiguous_singleton_sufficient.
intuition.
+
intuition.
eapply contiguous_adjacent_sufficient; auto.
eauto using contiguous_singleton_sufficient.
eapply IHl1.
*
eauto using sorted_subseq, subseq_skip, subseq_refl.
*
eauto using cons_contiguous_sorted.
Admitted.

Lemma rev_exists : forall A (l : list A) l', (exists l'', l = l'' ++ l') -> exists l'', rev l = rev l' ++ l''.
Proof using.
intros.
break_exists.
exists (rev x).
subst.
Admitted.

Lemma app_in_2 : forall A l l1 l2 (x : A), l = l1 ++ l2 -> In x l2 -> In x l.
Proof using.
intros.
subst.
Admitted.

Lemma app_contiguous_maxIndex_le_eq : forall l l1 l2 l2' i, l = l1 ++ l2 -> Prefix l2 l2' -> contiguous_range_exact_lo l i -> maxIndex l2' <= i -> l = l1.
Proof using.
intros.
subst.
destruct l2; eauto using app_nil_r.
simpl in *.
break_match; intuition.
subst.
simpl in *.
unfold contiguous_range_exact_lo in *.
intuition.
specialize (H0 e0).
conclude_using intuition.
Admitted.

Lemma sorted_app_1 : forall l1 l2, sorted (l1 ++ l2) -> sorted l1.
Proof using.
intros.
Admitted.

Lemma Prefix_maxIndex : forall l l' e, sorted l' -> Prefix l l' -> In e l -> eIndex e <= maxIndex l'.
Proof using.
induction l; intros; simpl in *; intuition; break_match; intuition; repeat subst; simpl in *; auto.
intuition.
eapply_prop_hyp sorted sorted; eauto.
match goal with | _ : eIndex _ <= maxIndex ?l |- _ => destruct l end.
-
simpl in *.
find_apply_lem_hyp Prefix_nil.
subst.
simpl in *.
intuition.
-
simpl in *.
Admitted.

Lemma app_maxIndex_In_l : forall l l' e, sorted (l ++ l') -> In e (l ++ l') -> maxIndex l' < eIndex e -> In e l.
Proof using.
induction l; intros; simpl in *; intuition.
-
destruct l'; simpl in *; intuition; subst; intuition.
find_apply_hyp_hyp.
intuition.
-
do_in_app.
intuition.
right.
eapply IHl; eauto.
Admitted.

Lemma contiguous_app_prefix_contiguous : forall l1 l2 l2' i, Prefix l2 l2' -> sorted (l1 ++ l2) -> contiguous_range_exact_lo (l1 ++ l2) i -> (l2 <> [] \/ i = maxIndex l2') -> contiguous_range_exact_lo l1 (maxIndex l2').
Proof using.
intros.
destruct l2.
-
intuition.
subst.
rewrite app_nil_r in *.
auto.
-
match goal with H : _ \/ _ |- _ => clear H end.
simpl in *.
break_match; intuition.
subst.
simpl.
Admitted.

Lemma sorted_term_index_lt : forall l e e', sorted l -> In e l -> In e' l -> eIndex e < eIndex e' -> eTerm e <= eTerm e'.
Proof using.
intros.
Admitted.

Lemma contiguous_app_prefix_2 : forall l l' l'' i, sorted (l ++ l') -> contiguous_range_exact_lo (l ++ l') 0 -> Prefix l' l'' -> maxIndex l'' < i <= maxIndex l -> exists e, eIndex e = i /\ In e l.
Proof using.
destruct l'.
-
intros.
simpl in *.
rewrite app_nil_r in *.
eapply_prop (contiguous_range_exact_lo l).
omega.
-
intros.
find_eapply_lem_hyp contiguous_app_prefix_contiguous; eauto.
left.
intuition.
Admitted.

Lemma contiguous_0_app : forall l1 l2 e, sorted (l1 ++ l2) -> contiguous_range_exact_lo (l1 ++ l2) 0 -> In e l1 -> eIndex e > maxIndex l2.
Proof using.
induction l1; intros.
-
simpl in *.
intuition.
-
rewrite <- app_comm_cons in *.
match goal with | H : In _ _ |- _ => simpl in H end.
intuition.
+
subst.
simpl in *.
intuition.
destruct l2; simpl in *.
*
unfold contiguous_range_exact_lo in *.
intuition.
*
match goal with | H : _ |- eIndex _ > eIndex ?e => specialize (H e) end.
conclude_using intuition.
intuition.
+
find_apply_lem_hyp cons_contiguous_sorted; eauto.
simpl in *.
Admitted.

Lemma deduplicate_log'_In_if : forall e l ks, In e (deduplicate_log' l ks) -> In e l.
Proof using.
induction l; intros; simpl in *; intuition.
Admitted.

Lemma findGtIndex_removeAfterIndex_i_lt_i' : forall l i i', sorted l -> i < i' -> (filter (fun x : entry => (i <? eIndex x) && (eIndex x <=? i')) (findGtIndex l i)) ++ removeAfterIndex l i = removeAfterIndex l i'.
Proof using.
induction l; intros; intuition.
simpl in *.
repeat break_if; simpl in *; repeat break_if; repeat (do_bool; intuition); try omega.
simpl.
f_equal.
rewrite IHl; eauto.
apply removeAfterIndex_eq.
intros.
find_apply_hyp_hyp.
Admitted.

Lemma findGtIndex_removeAfterIndex_i'_le_i : forall l i i', sorted l -> i' <= i -> (filter (fun x : entry => (i <? eIndex x) && (eIndex x <=? i')) (findGtIndex l i)) ++ removeAfterIndex l i = removeAfterIndex l i.
Proof using.
induction l; intros; intuition.
simpl in *.
Admitted.

Lemma sorted_cons_elim : forall e l, sorted (e :: l) -> sorted l.
Proof using.
Admitted.

Lemma contiguous_sorted_last : forall l x i, sorted (l ++ [x]) -> contiguous_range_exact_lo (l ++ [x]) i -> eIndex x = S i /\ contiguous_range_exact_lo l (S i).
Proof using.
Opaque sorted.
induction l; intros.
-
split.
+
simpl in *.
find_apply_lem_hyp contiguous_index_singleton.
assumption.
+
apply contiguous_nil.
-
destruct l.
+
simpl in *.
find_copy_apply_lem_hyp contiguous_index_adjacent; auto.
find_apply_lem_hyp cons_contiguous_sorted; auto.
find_copy_apply_lem_hyp contiguous_index_singleton.
intuition.
eapply contiguous_singleton_sufficient.
omega.
+
simpl in *.
find_copy_apply_lem_hyp contiguous_index_adjacent; auto.
find_apply_lem_hyp cons_contiguous_sorted; auto.
find_apply_lem_hyp sorted_cons_elim.
split.
*
eapply IHl; eauto.
*
eapply contiguous_adjacent_sufficient; intuition.
eapply IHl; eauto.
Admitted.

Lemma sorted_app_In_reduce: forall l1 l2 e1 e2, sorted (l1 ++ [e1]) -> sorted (l2 ++ [e2]) -> eIndex e1 = eIndex e2 -> (forall e, In e (l1 ++ [e1]) -> In e (l2 ++ [e2])) -> (forall e, In e l1 -> In e l2).
Proof using.
intros.
find_copy_eapply_lem_hyp (sorted_app_gt l1 [e1]); simpl; eauto.
assert (In e (l1 ++ [e1])).
apply in_or_app.
intuition.
find_apply_hyp_hyp.
find_apply_lem_hyp in_app_or.
intuition.
simpl in *.
intuition.
subst.
Admitted.

Lemma contiguous_sorted_subset_prefix : forall l1 l2 i, contiguous_range_exact_lo l1 i -> contiguous_range_exact_lo l2 i -> sorted l1 -> sorted l2 -> (forall e, In e l1 -> In e l2) -> Prefix (rev l1) (rev l2).
Proof using.
intros l1.
induction l1 using rev_ind; intuition.
induction l2 using rev_ind.
-
find_insterU.
conclude_using eauto.
contradiction.
-
repeat rewrite rev_unit.
find_apply_lem_hyp contiguous_sorted_last; auto.
find_apply_lem_hyp contiguous_sorted_last; auto.
intuition.
repeat find_reverse_rewrite.
simpl.
intuition.
+
eapply uniqueIndices_elim_eq; eauto using sorted_uniqueIndices.
+
Admitted.

Lemma not_empty_false : forall A (l : list A), not_empty l = false -> l = [].
Proof using.
Admitted.

Lemma moreUpToDate_refl : forall x y, moreUpToDate x y x y = true.
Proof using.
intros.
unfold moreUpToDate in *.
apply Bool.orb_true_intro.
right.
do_bool.
Admitted.

Lemma wonElection_dedup_spec : forall l, wonElection (dedup name_eq_dec l) = true -> exists quorum, NoDup quorum /\ length quorum > div2 (length nodes) /\ (forall h, In h quorum -> In h l).
Proof using.
intros.
exists (dedup name_eq_dec l).
intuition; eauto using NoDup_dedup, in_dedup_was_in.
unfold wonElection in *.
do_bool.
Admitted.

Lemma contiguous_findAtIndex : forall l s i, sorted l -> contiguous_range_exact_lo l s -> s < i <= maxIndex l -> exists e, findAtIndex l i = Some e.
Proof using.
unfold contiguous_range_exact_lo.
intros.
intuition.
match goal with | [ H : forall _, _ |- _ ] => specialize (H i) end.
intuition.
break_exists_exists.
intuition.
Admitted.

Lemma sorted_app_gt : forall l1 l2 e1 e2, sorted (l1 ++ l2) -> In e1 l1 -> In e2 l2 -> eIndex e1 > eIndex e2.
Proof using.
induction l1; intros.
-
contradiction.
-
simpl in *.
intuition.
+
subst.
assert (In e2 (l1 ++ l2)).
apply in_or_app.
intuition.
find_apply_hyp_hyp.
intuition.
+
eauto.
