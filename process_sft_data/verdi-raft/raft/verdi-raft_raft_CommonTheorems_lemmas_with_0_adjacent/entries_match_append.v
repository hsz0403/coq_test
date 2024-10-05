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

Lemma entries_match_append : forall xs ys es ple pli plt, sorted xs -> sorted ys -> sorted es -> entries_match xs ys -> (forall e1 e2, eIndex e1 = eIndex e2 -> eTerm e1 = eTerm e2 -> In e1 es -> In e2 ys -> (forall e3, eIndex e3 <= eIndex e1 -> In e3 es -> In e3 ys) /\ (pli <> 0 -> exists e4, eIndex e4 = pli /\ eTerm e4 = plt /\ In e4 ys)) -> (forall i, pli < i <= maxIndex es -> exists e, eIndex e = i /\ In e es) -> (forall e, In e es -> pli < eIndex e) -> findAtIndex xs pli = Some ple -> eTerm ple = plt -> pli <> 0 -> entries_match (es ++ removeAfterIndex xs pli) ys.
Proof using.
intros.
unfold entries_match.
intros.
split; intros.
-
in_crush_start.
+
match goal with | [ H : _ |- _ ] => solve [eapply H; eauto] end.
+
exfalso.
find_apply_lem_hyp removeAfterIndex_In_le; intuition.
find_apply_hyp_hyp.
omega.
+
find_apply_lem_hyp findAtIndex_elim.
intuition subst.
match goal with | [ H : forall _ _, _, H' : eIndex ?e1 = eIndex ?e2 |- _ ] => specialize (H e1 e2); do 4 concludes end.
intuition.
break_exists.
intuition.
find_copy_apply_lem_hyp removeAfterIndex_In_le; intuition.
find_apply_lem_hyp removeAfterIndex_in.
use_entries_match.
+
repeat find_apply_lem_hyp removeAfterIndex_in.
use_entries_match.
-
in_crush_start.
+
match goal with | [ H : forall _ _, _, H' : eIndex ?e1 = eIndex ?e2 |- _ ] => specialize (H e1 e2); do 4 concludes end.
intuition.
break_exists.
intuition.
destruct (le_lt_dec (eIndex e'') pli).
*
apply in_or_app.
right.
apply removeAfterIndex_le_In; auto.
find_apply_lem_hyp findAtIndex_elim.
intuition.
subst.
use_entries_match.
*
apply in_or_app.
left.
match goal with | H : forall _, _ < _ <= _ -> _ |- In ?e _ => specialize (H (eIndex e)) end.
intuition.
conclude_using ltac:(eapply le_trans; eauto; apply maxIndex_is_max; eauto).
break_exists.
intuition.
match goal with | _: eIndex ?e1 = eIndex ?e2 |- context [ ?e2 ] => eapply rachet with (x' := e1); eauto using sorted_uniqueIndices with * end.
+
apply in_or_app.
right.
find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto.
apply removeAfterIndex_le_In; [omega|].
find_apply_lem_hyp removeAfterIndex_in.
use_entries_match.
