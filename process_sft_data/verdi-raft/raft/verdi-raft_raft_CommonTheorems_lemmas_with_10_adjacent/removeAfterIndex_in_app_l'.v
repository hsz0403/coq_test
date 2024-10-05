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

Lemma findGtIndex_app_in_2 : forall l1 l2 e, sorted (l1 ++ l2) -> In e l2 -> exists l', findGtIndex (l1 ++ l2) (eIndex e) = l1 ++ l' /\ Prefix l' l2.
Proof using.
induction l1; intros; simpl in *; intuition.
-
eexists; intuition eauto using findGtIndex_Prefix.
-
break_if; simpl in *; intuition.
+
eapply_prop_hyp sorted sorted; eauto.
break_exists; intuition; find_rewrite; eauto.
+
do_bool.
specialize (H1 e); conclude H1 ltac:(apply in_app_iff; intuition).
Admitted.

Lemma findGtIndex_nil : forall l i, (forall e', In e' l -> eIndex e' <= i) -> findGtIndex l i = [].
Proof using.
intros; induction l; simpl in *; intuition.
break_if; do_bool; intuition.
specialize (H a); intuition.
Admitted.

Lemma findGtIndex_removeAfterIndex_commute : forall l i i', sorted l -> removeAfterIndex (findGtIndex l i) i' = findGtIndex (removeAfterIndex l i') i.
Proof using.
intros.
induction l; simpl in *; auto.
repeat (break_if; simpl; intuition); do_bool; try congruence.
symmetry.
apply findGtIndex_nil.
intros.
find_apply_lem_hyp removeAfterIndex_in.
find_apply_hyp_hyp.
Admitted.

Lemma findGtIndex_app_1 : forall l l' i, maxIndex l' <= i -> findGtIndex (l ++ l') i = findGtIndex l i.
Proof using.
induction l; intros; simpl in *; intuition.
-
destruct l'; simpl in *; intuition.
break_if; do_bool; auto; omega.
-
break_if; do_bool; auto.
f_equal.
Admitted.

Lemma findGtIndex_app_2 : forall l l' i, sorted (l ++ l') -> i < maxIndex l' -> findGtIndex (l ++ l') i = l ++ findGtIndex l' i.
Proof using.
induction l; intros; simpl in *; intuition.
break_if; do_bool; auto.
-
f_equal.
eauto.
-
exfalso.
destruct l'; simpl in *; intuition.
Admitted.

Lemma thing3 : forall l l' e, sorted (l ++ l') -> (forall e', In e' (l ++ l') -> eIndex e' > 0) -> In e (l ++ l') -> eIndex e <= maxIndex l' -> In e l'.
Proof using.
induction l; intros; simpl in *; intuition.
subst.
destruct l'; simpl in *; intuition.
-
exfalso.
specialize (H0 e).
intuition.
-
exfalso.
specialize (H3 e0).
conclude_using intuition.
Admitted.

Lemma findGtIndex_non_empty : forall l i, i < maxIndex l -> findGtIndex l i <> [].
Proof using.
intros.
induction l; simpl in *; intuition.
break_if; do_bool; simpl in *; intuition.
Admitted.

Lemma sorted_Prefix_in_eq : forall l' l, sorted l -> Prefix l' l -> (forall e, In e l -> In e l') -> l' = l.
Proof using.
induction l'; intros; simpl in *; intuition.
-
destruct l; simpl in *; auto.
specialize (H1 e); intuition.
-
break_match; intuition.
subst.
simpl in *.
intuition.
f_equal.
eapply IHl'; eauto.
intros.
specialize (H1 e0); intuition.
subst.
specialize (H0 e0); intuition.
Admitted.

Lemma removeAfterIndex_eq : forall l i, (forall e, In e l -> eIndex e <= i) -> removeAfterIndex l i = l.
Proof using.
induction l; intros; simpl in *; intuition.
break_if; intuition.
do_bool.
specialize (H a).
intuition.
Admitted.

Lemma removeAfterIndex_in_app : forall l l' e, In e l -> removeAfterIndex (l ++ l') (eIndex e) = (removeAfterIndex l (eIndex e)) ++ l'.
Proof using.
induction l; intros; simpl in *; intuition; subst; break_if; do_bool; eauto using app_ass.
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

Lemma removeAfterIndex_in_app_l' : forall l l' e, (forall e', In e' l -> eIndex e' > eIndex e) -> In e l' -> removeAfterIndex (l ++ l') (eIndex e) = removeAfterIndex l' (eIndex e).
Proof using.
induction l; intros; simpl in *; intuition; subst; break_if; do_bool; eauto using app_ass.
specialize (H a).
intuition.
omega.
