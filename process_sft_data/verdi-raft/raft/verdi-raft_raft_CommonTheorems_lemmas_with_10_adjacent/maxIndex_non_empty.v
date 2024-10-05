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

Lemma uniqueIndices_elim_eq : forall xs x y, uniqueIndices xs -> In x xs -> In y xs -> eIndex x = eIndex y -> x = y.
Proof using.
unfold uniqueIndices.
Admitted.

Lemma sorted_cons : forall xs a, sorted xs -> (forall a', In a' xs -> eIndex a > eIndex a' /\ eTerm a >= eTerm a') -> sorted (a :: xs).
Proof using.
intros.
simpl in *.
Admitted.

Lemma sorted_subseq : forall ys xs, subseq xs ys -> sorted ys -> sorted xs.
Proof using.
induction ys; intros; simpl in *.
-
break_match; intuition.
-
break_match; intuition.
subst.
apply sorted_cons; eauto.
intros.
Admitted.

Theorem maxTerm_is_max : forall l e, sorted l -> In e l -> maxTerm l >= eTerm e.
Proof using.
induction l; intros.
-
simpl in *.
intuition.
-
simpl in *.
intuition.
+
subst.
auto with *.
+
find_apply_hyp_hyp.
Admitted.

Theorem maxIndex_is_max : forall l e, sorted l -> In e l -> maxIndex l >= eIndex e.
Proof using.
induction l; intros.
-
simpl in *.
intuition.
-
simpl in *.
intuition.
+
subst.
auto with *.
+
find_apply_hyp_hyp.
Admitted.

Theorem S_maxIndex_not_in : forall l e, sorted l -> eIndex e = S (maxIndex l) -> ~ In e l.
Proof using.
intros.
intro.
find_apply_lem_hyp maxIndex_is_max; auto.
subst.
Admitted.

Lemma removeAfterIndex_subseq : forall l i, subseq (removeAfterIndex l i) l.
Proof using.
induction l; intros; simpl; auto.
repeat break_match; intuition.
-
find_inversion.
eauto using subseq_refl.
-
right.
find_reverse_rewrite.
Admitted.

Lemma removeAfterIndex_sorted : forall l i, sorted l -> sorted (removeAfterIndex l i).
Proof using.
intros.
Admitted.

Lemma removeAfterIndex_in : forall l i a, In a (removeAfterIndex l i) -> In a l.
Proof using.
Admitted.

Lemma findAtIndex_not_in : forall l e, sorted l -> findAtIndex l (eIndex e) = None -> ~ In e l.
Proof using.
induction l; intros; intro.
-
intuition.
-
simpl in *.
break_match; try discriminate.
intuition.
+
subst.
rewrite <- beq_nat_refl in *.
discriminate.
+
find_copy_apply_hyp_hyp.
intuition.
break_if; do_bool; eauto.
Admitted.

Lemma findAtIndex_in : forall l i e', findAtIndex l i = Some e' -> In e' l.
Proof using.
induction l; intros.
-
discriminate.
-
simpl in *.
break_match.
+
find_inversion.
auto.
+
Admitted.

Lemma findAtIndex_index : forall l i e', findAtIndex l i = Some e' -> i = eIndex e'.
Proof using.
induction l; intros.
-
discriminate.
-
simpl in *.
break_match.
+
find_inversion.
apply beq_nat_true in Heqb.
auto.
+
Admitted.

Lemma NoDup_removeAfterIndex : forall l i, NoDup l -> NoDup (removeAfterIndex l i).
Proof using.
Admitted.

Lemma removeAfterIndex_le_In : forall xs i x, eIndex x <= i -> In x xs -> In x (removeAfterIndex xs i).
Proof using.
induction xs; intros.
-
intuition.
-
simpl in *.
break_if; simpl in *; intuition.
subst.
do_bool.
Admitted.

Lemma removeAfterIndex_In_le : forall xs i x, sorted xs -> In x (removeAfterIndex xs i) -> eIndex x <= i.
Proof using.
induction xs; intros.
-
simpl in *.
intuition.
-
simpl in *.
break_if; simpl in *; do_bool; intuition; subst; auto.
find_apply_hyp_hyp.
Admitted.

Lemma removeAfterIndex_covariant : forall xs ys i x, sorted xs -> sorted ys -> In x (removeAfterIndex xs i) -> (forall x, In x xs -> In x ys) -> In x (removeAfterIndex ys i).
Proof using.
induction xs; intros.
-
simpl in *.
intuition.
-
simpl in *.
break_match; simpl in *; intuition; subst; do_bool; match goal with | e : entry, H : forall _, _ = _ \/ _ -> _ |- _ => specialize (H e) end; intuition.
+
eauto using removeAfterIndex_le_In.
+
find_apply_hyp_hyp.
intuition.
match goal with | _ : eIndex ?e <= ?li, _ : eIndex ?e > eIndex ?e' |- _ => assert (eIndex e' <= li) by omega end.
Admitted.

Lemma maxIndex_non_empty : forall l, l <> nil -> exists e, In e l /\ maxIndex l = eIndex e /\ maxTerm l = eTerm e.
Proof using.
destruct l; intros; simpl in *; eauto; congruence.
