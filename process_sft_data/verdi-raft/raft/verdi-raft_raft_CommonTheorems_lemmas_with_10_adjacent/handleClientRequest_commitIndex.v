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

Lemma applied_entries_safe_update : forall sigma h st, lastApplied st = lastApplied (sigma h) -> removeAfterIndex (log st) (lastApplied (sigma h)) = removeAfterIndex (log (sigma h)) (lastApplied (sigma h)) -> applied_entries (update name_eq_dec sigma h st) = applied_entries sigma.
Proof using.
intros.
unfold applied_entries in *.
repeat break_match; repeat find_rewrite; intuition; match goal with | _ : argmax ?f ?l = _, _ : argmax ?g ?l = _ |- _ => assert (argmax f l = argmax g l) by (apply argmax_fun_ext; intros; update_destruct; subst; rewrite_update; auto) end; repeat find_rewrite; try congruence.
match goal with | H : Some _ = Some _ |- _ => inversion H end.
subst.
clean.
f_equal.
Admitted.

Lemma applied_entries_log_lastApplied_same : forall sigma sigma', (forall h, log (sigma' h) = log (sigma h)) -> (forall h, lastApplied (sigma' h) = lastApplied (sigma h)) -> applied_entries sigma' = applied_entries sigma.
Proof using.
intros.
unfold applied_entries in *.
rewrite argmax_fun_ext with (g := fun h : name => lastApplied (sigma h)); intuition.
break_match; auto.
repeat find_higher_order_rewrite.
Admitted.

Lemma applied_entries_log_lastApplied_update_same : forall sigma h st, log st = log (sigma h) -> lastApplied st = lastApplied (sigma h) -> applied_entries (update name_eq_dec sigma h st) = applied_entries sigma.
Proof using.
intros.
Admitted.

Lemma applied_entries_cases : forall sigma, applied_entries sigma = [] \/ exists h, applied_entries sigma = rev (removeAfterIndex (log (sigma h)) (lastApplied (sigma h))).
Proof using.
intros.
unfold applied_entries in *.
Admitted.

Lemma removeAfterIndex_partition : forall l x, exists l', l = l' ++ removeAfterIndex l x.
Proof using.
intros; induction l; simpl in *; intuition eauto using app_nil_r.
break_exists.
break_if; [exists nil; eauto|].
do_bool.
Admitted.

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
Admitted.

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
Admitted.

Lemma doLeader_appliedEntries : forall sigma h os st' ms, doLeader (sigma h) h = (os, st', ms) -> applied_entries (update name_eq_dec sigma h st') = applied_entries sigma.
Proof using.
intros.
apply applied_entries_log_lastApplied_same.
-
intros.
update_destruct; subst; rewrite_update; auto.
eapply doLeader_same_log; eauto.
-
intros.
update_destruct; subst; rewrite_update; auto.
unfold doLeader in *.
Admitted.

Lemma applyEntries_spec : forall es h st os st', applyEntries h st es = (os, st') -> exists d cc, st' = {[ {[ st with stateMachine := d ]} with clientCache := cc ]}.
Proof using.
induction es; intros; simpl in *; intuition.
-
find_inversion.
destruct st'; repeat eexists; eauto.
-
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma applyEntries_spec_ind : forall {es h st os st'}, applyEntries h st es = (os, st') -> forall P : raft_data -> Prop, (forall d cc, P {[ {[ st with stateMachine := d ]} with clientCache := cc ]}) -> P st'.
Proof using.
intros.
find_apply_lem_hyp applyEntries_spec.
break_exists.
subst.
Admitted.

Lemma handleTimeout_commitIndex : forall h st out st' l, handleTimeout h st = (out, st', l) -> commitIndex st' = commitIndex st.
Proof using.
Admitted.

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

Lemma handleClientRequest_commitIndex : forall h st client id c out st' l, handleClientRequest h st client id c = (out, st', l) -> commitIndex st' = commitIndex st.
Proof using.
unfold handleClientRequest.
intros.
repeat break_match; find_inversion; auto.
