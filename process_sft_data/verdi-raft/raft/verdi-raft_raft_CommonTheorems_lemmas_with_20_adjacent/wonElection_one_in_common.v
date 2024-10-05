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

Lemma argmin_one_different : forall A (A_eq_dec : forall x y : A, {x = y} + {x <> y}) f g (l : list A) a, (forall x, In x l -> a <> x -> f x = g x) -> (forall x, In x l -> g x <= f x) -> (argmin g l = argmin f l \/ argmin g l = Some a).
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
find_apply_lem_hyp argmin_in; intuition.
destruct (A_eq_dec a a1); destruct (A_eq_dec a a0); repeat subst; intuition; specialize (H0 a1); specialize (H a0); intuition; repeat find_rewrite; omega.
+
do_bool.
right.
find_apply_lem_hyp argmin_in; intuition.
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
repeat find_apply_lem_hyp argmin_elim; intuition.
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
Admitted.

Lemma applied_entries_update : forall sigma h st, lastApplied st >= lastApplied (sigma h) -> (applied_entries (update name_eq_dec sigma h st) = applied_entries sigma /\ (exists h', argmax (fun h => lastApplied (sigma h)) (all_fin N) = Some h' /\ lastApplied (sigma h') >= lastApplied st)) \/ (argmax (fun h' => lastApplied (update name_eq_dec sigma h st h')) (all_fin N) = Some h /\ applied_entries (update name_eq_dec sigma h st) = (rev (removeAfterIndex (log st) (lastApplied st)))).
Proof using.
intros.
unfold applied_entries in *.
repeat break_match; intuition; try solve [find_apply_lem_hyp argmax_None; exfalso; pose proof (all_fin_all _ h); find_rewrite; intuition].
match goal with | _ : argmax ?f ?l = _, _ : argmax ?g ?l = _ |- _ => pose proof argmax_one_different name name_eq_dec g f l h as Hproof end.
forward Hproof; [intros; rewrite_update; intuition|]; concludes.
forward Hproof; [intros; update_destruct; subst; rewrite_update; intuition|]; concludes.
intuition.
-
repeat find_rewrite.
find_inversion.
update_destruct; subst; rewrite_update; intuition.
left.
intuition.
eexists; intuition eauto.
repeat find_apply_lem_hyp argmax_elim; intuition eauto.
match goal with H : _ |- _ => solve [specialize (H h); rewrite_update; eauto using all_fin_all] end.
-
repeat find_rewrite.
find_inversion.
rewrite_update.
Admitted.

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

Lemma handleClientRequest_commitIndex : forall h st client id c out st' l, handleClientRequest h st client id c = (out, st', l) -> commitIndex st' = commitIndex st.
Proof using.
unfold handleClientRequest.
intros.
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

Lemma wonElection_one_in_common : forall l l', wonElection (dedup name_eq_dec l) = true -> wonElection (dedup name_eq_dec l') = true -> exists h, In h l /\ In h l'.
Proof using.
intros.
unfold wonElection in *.
do_bool.
cut (exists h, In h (dedup name_eq_dec l) /\ In h (dedup name_eq_dec l')); [intros; break_exists; exists x; intuition eauto using in_dedup_was_in|].
eapply pigeon with (l := nodes); eauto using all_fin_all, all_fin_NoDup, NoDup_dedup, name_eq_dec, div2_correct.
