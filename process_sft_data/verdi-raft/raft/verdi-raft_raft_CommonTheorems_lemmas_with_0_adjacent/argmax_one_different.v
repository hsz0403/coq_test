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
omega.
