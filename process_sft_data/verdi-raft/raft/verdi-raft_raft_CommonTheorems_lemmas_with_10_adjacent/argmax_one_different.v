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

Lemma handleAppendEntriesReply_same_log : forall n st src t es b st' l, handleAppendEntriesReply n st src t es b = (st', l) -> log st' = log st.
Proof using.
intros.
unfold handleAppendEntriesReply in *.
Admitted.

Lemma handleAppendEntriesReply_same_lastApplied : forall n st src t es b st' l, handleAppendEntriesReply n st src t es b = (st', l) -> lastApplied st' = lastApplied st.
Proof using.
intros.
unfold handleAppendEntriesReply in *.
Admitted.

Lemma handleAppendEntries_same_lastApplied : forall h st t n pli plt es ci st' ps, handleAppendEntries h st t n pli plt es ci = (st', ps) -> lastApplied st' = lastApplied st.
Proof using.
intros.
unfold handleAppendEntries in *.
Admitted.

Lemma wonElection_length : forall l1 l2, wonElection l1 = true -> length l1 <= length l2 -> wonElection l2 = true.
Proof using.
intros.
unfold wonElection in *.
do_bool.
Admitted.

Lemma wonElection_no_dup_in : forall l1 l2, wonElection l1 = true -> NoDup l1 -> (forall x, In x l1 -> In x l2) -> wonElection l2 = true.
Proof using.
intros.
Admitted.

Lemma wonElection_exists_voter : forall l, wonElection l = true -> exists x, In x l.
Proof using.
unfold wonElection.
intros.
destruct l; try discriminate.
simpl.
Admitted.

Lemma argmax_fun_ext : forall A (f : A -> nat) g l, (forall a, f a = g a) -> argmax f l = argmax g l.
Proof using.
intros.
induction l; simpl in *; intuition.
find_rewrite.
break_match; intuition.
repeat find_higher_order_rewrite.
Admitted.

Lemma argmax_None : forall A (f : A -> nat) l, argmax f l = None -> l = [].
Proof using.
intros.
destruct l; simpl in *; intuition.
Admitted.

Lemma argmax_elim : forall A (f : A -> nat) l a, argmax f l = Some a -> (In a l /\ forall x, In x l -> f a >= f x).
Proof using.
induction l; intros; simpl in *; [congruence|].
repeat break_match; find_inversion.
-
do_bool.
match goal with | H : forall _, Some ?a = Some _ -> _ |- _ => specialize (H a) end.
intuition; subst; auto.
find_apply_hyp_hyp.
omega.
-
do_bool.
match goal with | H : forall _, Some ?a = Some _ -> _ |- _ => specialize (H a) end.
intuition; subst; auto.
find_apply_hyp_hyp.
omega.
-
intuition; subst; auto.
find_apply_lem_hyp argmax_None.
subst.
Admitted.

Lemma argmax_in : forall A (f : A -> nat) l a, argmax f l = Some a -> In a l.
Proof using.
intros.
find_apply_lem_hyp argmax_elim.
Admitted.

Lemma argmin_fun_ext : forall A (f : A -> nat) g l, (forall a, f a = g a) -> argmin f l = argmin g l.
Proof using.
intros.
induction l; simpl in *; intuition.
find_rewrite.
break_match; intuition.
repeat find_higher_order_rewrite.
Admitted.

Lemma argmin_None : forall A (f : A -> nat) l, argmin f l = None -> l = [].
Proof using.
intros.
destruct l; simpl in *; intuition.
Admitted.

Lemma argmin_elim : forall A (f : A -> nat) l a, argmin f l = Some a -> (In a l /\ forall x, In x l -> f a <= f x).
Proof using.
induction l; intros; simpl in *; [congruence|].
repeat break_match; find_inversion.
-
do_bool.
match goal with | H : forall _, Some ?a = Some _ -> _ |- _ => specialize (H a) end.
intuition; subst; auto.
find_apply_hyp_hyp.
omega.
-
do_bool.
match goal with | H : forall _, Some ?a = Some _ -> _ |- _ => specialize (H a) end.
intuition; subst; auto.
find_apply_hyp_hyp.
omega.
-
intuition; subst; auto.
find_apply_lem_hyp argmin_None.
subst.
Admitted.

Lemma argmin_in : forall A (f : A -> nat) l a, argmin f l = Some a -> In a l.
Proof using.
intros.
find_apply_lem_hyp argmin_elim.
Admitted.

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
