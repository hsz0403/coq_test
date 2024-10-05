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

Lemma entries_match_scratch : forall es ys plt, sorted es -> uniqueIndices ys -> (forall e1 e2, eIndex e1 = eIndex e2 -> eTerm e1 = eTerm e2 -> In e1 es -> In e2 ys -> (forall e3, eIndex e3 <= eIndex e1 -> In e3 es -> In e3 ys) /\ (0 <> 0 -> exists e4, eIndex e4 = 0 /\ eTerm e4 = plt /\ In e4 ys)) -> (forall i, 0 < i <= maxIndex es -> exists e, eIndex e = i /\ In e es) -> (forall e, In e es -> 0 < eIndex e) -> (forall y, In y ys -> 0 < eIndex y) -> entries_match es ys.
Proof using.
intros.
unfold entries_match.
intuition.
-
match goal with | [ H : _ |- _ ] => solve [eapply H; eauto] end.
-
match goal with | [ H : forall _ _, _, H' : eIndex ?e1 = eIndex ?e2 |- _ ] => specialize (H e1 e2); do 4 concludes end.
intuition.
match goal with | [ H : forall _, _ < _ <= _ -> _, _ : eIndex ?e3 <= eIndex _ |- _ ] => specialize (H (eIndex e3)); conclude H ltac:(split; [eauto| eapply le_trans; eauto; apply maxIndex_is_max; eauto]) end.
break_exists.
intuition.
match goal with | [ _ : In ?x _, _ : eIndex ?x = eIndex ?e3, _ : eIndex ?e3 <= eIndex _ |- _ ] => eapply rachet with (x' := x); eauto using sorted_uniqueIndices end.
match goal with | [ H : _ |- _ ] => solve [ eapply H; eauto; congruence ] end.
