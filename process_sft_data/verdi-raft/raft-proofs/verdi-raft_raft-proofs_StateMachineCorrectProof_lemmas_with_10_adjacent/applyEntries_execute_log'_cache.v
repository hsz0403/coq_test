Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.DecompositionWithPostState.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.StateMachineCorrectInterface.
Section StateMachineCorrect.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {si : sorted_interface}.
Context {misi : max_index_sanity_interface}.
Context {smsi : state_machine_safety_interface}.
Context {lmi : log_matching_interface}.
Ltac get_invariant_pre inv := match goal with | H : raft_intermediate_reachable _ |- _=> match (type of H) with | context [mkNetwork] => fail 2 end || copy_apply inv H end.
Ltac get_invariant_post inv := match goal with | H : raft_intermediate_reachable _ |- _=> match (type of H) with | context [mkNetwork] => copy_apply inv H end end.
Definition clientCache_to_ks (c : list (clientId * (nat * output))) := map (fun e => (fst e, fst (snd e))) c.
Fixpoint log_to_ks' (l : list entry) (ks : list (clientId * nat)) : list (clientId * nat) := match l with | e :: l' => if (assoc_default clientId_eq_dec ks (eClient e) 0) <=? eId e then log_to_ks' l' (assoc_set clientId_eq_dec ks (eClient e) (eId e)) else log_to_ks' l' ks | [] => ks end.
Definition log_to_ks l := log_to_ks' l [].
Definition client_cache_keys_correct net := forall h, a_equiv clientId_eq_dec (clientCache_to_ks (clientCache (nwState net h))) (log_to_ks' (rev (removeAfterIndex (log (nwState net h)) (lastApplied (nwState net h)))) []).
Fixpoint max_id_for_client_default (default : nat) (c : clientId) (l : list entry) : nat := match l with | [] => default | e :: l' => if clientId_eq_dec c (eClient e) then max_id_for_client_default (max default (eId e)) c l' else max_id_for_client_default default c l' end.
Ltac use_same_client_cache hyp := erewrite same_clientCache_same_getLastId in *; [|eapply hyp]; eauto.
Instance smci : state_machine_correct_interface.
Proof.
split.
exact state_machine_correct_invariant.
End StateMachineCorrect.

Lemma removeAfterIndex_cons : forall l x i, i < eIndex x -> removeAfterIndex (x :: l) i = removeAfterIndex l i.
Proof using.
intros.
Admitted.

Lemma handleClientRequest_preserves_lastApplied_entries: forall h (net : network) (d : raft_data) client id c out l, raft_intermediate_reachable net -> handleClientRequest h (nwState net h) client id c = (out, d, l) -> removeAfterIndex (log d) (lastApplied d) = removeAfterIndex (log (nwState net h)) (lastApplied (nwState net h)).
Proof using misi.
intros.
erewrite handleClientRequest_lastApplied; eauto.
find_apply_lem_hyp handleClientRequest_log.
intuition; repeat find_rewrite; eauto.
break_exists; intuition; repeat find_rewrite.
erewrite removeAfterIndex_cons; eauto.
get_invariant_pre max_index_sanity_invariant.
unfold maxIndex_sanity, maxIndex_lastApplied in *.
intuition.
match goal with | H : forall _, lastApplied _ <= maxIndex _ |- _ => specialize (H h) end.
Admitted.

Lemma client_cache_keys_correct_clientCache_complete : forall net, client_cache_keys_correct net -> client_cache_complete net.
Proof using.
unfold client_cache_keys_correct, client_cache_complete.
intros.
unfold getLastId.
enough (exists id, assoc clientId_eq_dec (clientCache_to_ks (clientCache (nwState net h))) (eClient e) = Some id /\ eId e <= id).
-
break_exists_exists.
intuition.
find_apply_lem_hyp clientCache_to_ks_assoc.
break_exists_exists.
intuition.
-
erewrite assoc_a_equiv by eauto.
find_apply_lem_hyp in_rev.
Admitted.

Lemma deduplicate_log'_app : forall l1 l2 ks, deduplicate_log' (l1 ++ l2) ks = deduplicate_log' l1 ks ++ (deduplicate_log' l2 (log_to_ks' l1 ks)).
Proof using.
induction l1; intros; simpl in *; auto.
repeat break_match; simpl in *; eauto; try solve [f_equal; eauto].
-
exfalso.
do_bool.
find_erewrite_lem assoc_assoc_default.
omega.
-
do_bool.
find_erewrite_lem assoc_assoc_default.
rewrite assoc_set_same; eauto.
find_eapply_lem_hyp le_antisym; eauto.
subst.
auto.
-
exfalso.
do_bool.
find_erewrite_lem assoc_assoc_default_missing.
Admitted.

Lemma deduplicate_log'_a_equiv : forall l ks ks', a_equiv clientId_eq_dec ks ks' -> deduplicate_log' l ks = deduplicate_log' l ks'.
Proof using.
induction l; intros; simpl in *; auto.
Admitted.

Lemma cacheApplyEntry_getLastId : forall st e l st' client id out, cacheApplyEntry st e = (l, st') -> getLastId st' client = Some (id, out) -> getLastId st client = Some (id, out) \/ eClient e = client /\ l = [out] /\ eId e = id /\ out = fst (handler (eInput e) (stateMachine st)) /\ (forall id' out', getLastId st client = Some (id', out') -> id' < id).
Proof using.
intros.
unfold cacheApplyEntry in *.
repeat break_match; try find_inversion; subst; auto; do_bool.
-
unfold applyEntry in *.
break_let.
find_inversion.
simpl in *.
match goal with | H : context [assoc_set] |- _ => unfold getLastId in H; simpl in H end.
destruct (clientId_eq_dec client (eClient e)); try now rewrite get_set_diff in *; auto.
subst.
rewrite get_set_same in *.
find_inversion.
repeat find_rewrite.
right.
intuition.
find_inversion.
omega.
-
unfold applyEntry in *.
break_let.
find_inversion.
simpl in *.
match goal with | H : context [assoc_set] |- _ => unfold getLastId in H; simpl in H end.
destruct (clientId_eq_dec client (eClient e)); try now rewrite get_set_diff in *; auto.
subst.
rewrite get_set_same in *.
find_inversion.
repeat find_rewrite.
right.
intuition.
Admitted.

Lemma applyEntries_app : forall l h st os d l', applyEntries h st (l ++ l') = (os, d) -> exists os' os'' d', applyEntries h st l = (os', d') /\ applyEntries h d' l' = (os'', d) /\ os = os' ++ os''.
Proof using.
induction l; intros; simpl in *; try now repeat eexists; eauto.
repeat break_let.
find_inversion.
find_apply_hyp_hyp.
break_exists.
intuition.
repeat find_rewrite.
find_inversion.
Admitted.

Lemma getLastId_clientCache_to_ks_assoc : forall (st : RaftState.raft_data term name entry logIndex serverType data clientId output) (client : clientId) (id : nat) o, getLastId st client = Some (id, o) -> assoc clientId_eq_dec (clientCache_to_ks (clientCache st)) client = Some id.
Proof using.
intros.
unfold getLastId in *.
induction (clientCache st).
-
simpl in *.
congruence.
-
simpl in *.
break_let.
subst.
simpl in *.
Admitted.

Lemma i_lt_assoc_default_0 : forall K K_eq_dec ks (k : K) i, i < assoc_default K_eq_dec ks k 0 -> exists i', assoc K_eq_dec ks k = Some i' /\ i < i'.
Proof using.
intros.
unfold assoc_default in *.
Admitted.

Lemma applyEntries_log_to_ks' : forall l h st o st', applyEntries h st l = (o, st') -> a_equiv clientId_eq_dec (clientCache_to_ks (clientCache st')) (log_to_ks' l (clientCache_to_ks (clientCache st))).
Proof using.
induction l; intros; simpl in *; intuition.
-
find_inversion.
apply a_equiv_refl.
-
repeat break_let.
find_inversion.
break_if.
+
do_bool.
unfold cacheApplyEntry in *.
repeat break_match; repeat find_inversion; do_bool.
*
find_apply_lem_hyp getLastId_clientCache_to_ks_assoc.
find_erewrite_lem assoc_assoc_default.
omega.
*
find_apply_hyp_hyp.
subst.
rewrite assoc_set_same; eauto using a_equiv_refl.
eauto using getLastId_clientCache_to_ks_assoc.
*
subst.
unfold applyEntry in *.
break_let.
find_inversion.
find_apply_hyp_hyp.
eapply a_equiv_trans; eauto.
simpl.
erewrite clientCache_to_ks_assoc_set; eauto using a_equiv_refl.
*
subst.
unfold applyEntry in *.
break_let.
find_inversion.
find_apply_hyp_hyp.
eapply a_equiv_trans; eauto.
simpl.
erewrite clientCache_to_ks_assoc_set; eauto using a_equiv_refl.
+
do_bool.
find_apply_lem_hyp i_lt_assoc_default_0.
break_exists.
intuition.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
break_exists.
unfold cacheApplyEntry in *.
repeat find_rewrite.
break_if; do_bool; try omega.
find_inversion.
Admitted.

Lemma doGenericServer_spec : forall (orig_base_params : BaseParams) (one_node_params : OneNodeParams orig_base_params) (raft_params : RaftParams orig_base_params) (h : name) (st : raft_data) (os : list raft_output) (st' : raft_data) (ps : list (name * msg)), doGenericServer h st = (os, st', ps) -> st' = st \/ log st' = log st /\ lastApplied st < lastApplied st' /\ lastApplied st' = commitIndex st /\ exists os' st'', applyEntries h st (rev (filter (fun x : entry => (lastApplied st <? eIndex x) && (eIndex x <=? commitIndex st)) (findGtIndex (log st) (lastApplied st)))) = (os', st'') /\ clientCache st' = clientCache st'' /\ forall c, getLastId st' c = getLastId st'' c.
Proof using.
intros.
unfold doGenericServer in *.
break_let.
break_if.
-
right.
do_bool.
find_inversion.
simpl in *.
intuition; eauto; use_applyEntries_spec; subst; simpl in *; auto.
-
left.
do_bool.
find_inversion.
match goal with | _ : applyEntries _ _ (rev ?l) = _ |- _ => enough (l = []) by (repeat find_rewrite; simpl in *; find_inversion; destruct r; simpl in *; auto) end.
erewrite filter_fun_ext_eq; eauto using filter_false.
intros.
simpl in *.
apply Bool.not_true_is_false.
intuition.
do_bool.
intuition.
do_bool.
use_applyEntries_spec.
subst.
simpl in *.
Admitted.

Lemma deduplicate_log_app : forall l l', exists l'', deduplicate_log (l ++ l') = deduplicate_log l ++ l''.
Proof using.
Admitted.

Lemma output_correct_monotonic : forall c i o xs ys, output_correct c i o xs -> output_correct c i o (xs ++ ys).
Proof using.
unfold output_correct.
intros.
break_exists.
intuition.
pose proof (deduplicate_log_app xs ys).
break_exists.
repeat find_rewrite.
rewrite app_ass in *.
simpl in *.
eexists.
eexists.
eexists.
eexists.
eexists.
Admitted.

Lemma execute_log'_trace: forall l d d' tr tr' tr'', execute_log' l d tr = (tr', d') -> execute_log' l d (tr'' ++ tr) = (tr'' ++ tr', d').
Proof using.
induction l; intros; simpl in *.
-
find_inversion.
auto.
-
repeat break_let.
rewrite app_ass.
Admitted.

Lemma execute_log'_trace_nil: forall l d d' tr' tr'', execute_log' l d [] = (tr', d') -> execute_log' l d tr'' = (tr'' ++ tr', d').
Proof using.
intros.
Admitted.

Lemma hd_error_Some_app : forall A l l' (x : A), hd_error l = Some x -> hd_error (l ++ l') = Some x.
Proof using.
intros.
Admitted.

Lemma client_cache_keys_correct_do_generic_server : raft_net_invariant_do_generic_server' client_cache_keys_correct.
Proof using si.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_apply_lem_hyp doGenericServer_spec.
intuition; repeat find_rewrite; eauto.
break_exists.
intuition.
find_apply_lem_hyp applyEntries_log_to_ks'.
repeat find_rewrite.
eapply a_equiv_trans; eauto.
get_invariant_pre logs_sorted_invariant.
unfold logs_sorted in *; intuition.
erewrite removeAfterIndex_app; eauto.
rewrite rev_app_distr.
rewrite log_to_ks'_app.
match goal with | |- a_equiv _ (_ (_ ?l) _) (_ (_ ?l') _) => enough (l = l') by (repeat find_rewrite; now apply log_to_ks'_a_equiv) end.
apply filter_fun_ext_eq.
intros.
rewrite <- Bool.andb_true_l.
f_equal.
apply Nat.ltb_lt.
find_apply_lem_hyp findGtIndex_necessary.
Admitted.

Lemma client_cache_keys_correct_append_entries : raft_net_invariant_append_entries' client_cache_keys_correct.
Proof using lmi smsi misi si.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleAppendEntries_clientCache; eauto.
Admitted.

Lemma client_cache_keys_correct_append_entries_reply : raft_net_invariant_append_entries_reply' client_cache_keys_correct.
Proof using.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleAppendEntriesReply_clientCache; eauto.
erewrite handleAppendEntriesReply_log; eauto.
Admitted.

Lemma client_cache_keys_correct_request_vote : raft_net_invariant_request_vote' client_cache_keys_correct.
Proof using.
red.
unfold client_cache_keys_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
erewrite handleRequestVote_clientCache; eauto.
erewrite handleRequestVote_same_log; eauto.
Admitted.

Lemma applyEntries_execute_log'_cache : forall l h st os st' client id out, applyEntries h st l = (os, st') -> getLastId st' client = Some (id, out) -> (getLastId st client = Some (id, out) \/ exists e xs ys, deduplicate_log' l (clientCache_to_ks (clientCache st)) = xs ++ e :: ys /\ eClient e = client /\ eId e = id /\ Some (eInput e, out) = hd_error (rev (fst (execute_log' (xs ++ [e]) (stateMachine st) [])))).
Proof using.
induction l using rev_ind; intros; simpl in *; intuition; repeat break_let; repeat find_inversion; auto.
find_apply_lem_hyp applyEntries_app.
break_exists.
intuition.
simpl in *.
break_let.
find_inversion.
unfold cacheApplyEntry in *.
repeat break_match.
-
subst.
find_inversion.
copy_eapply_prop_hyp applyEntries applyEntries; [| match goal with | H : context [id] |- _ => apply H end].
intuition.
right.
break_exists_name e; exists e.
break_exists_name xs.
exists xs.
break_exists_name ys.
break_exists.
intuition.
subst.
match goal with | _ : deduplicate_log' ?l ?ks = _ |- _ => pose proof deduplicate_log'_app l [x] ks end.
repeat find_rewrite.
repeat eexists; eauto.
rewrite app_ass.
rewrite <- app_comm_cons.
eauto.
-
do_bool.
repeat find_inversion.
copy_eapply_prop_hyp applyEntries applyEntries; [| match goal with | H : context [id] |- _ => apply H end].
intuition.
right.
break_exists_name e; exists e.
break_exists_name xs.
exists xs.
break_exists_name ys.
break_exists.
intuition.
subst.
match goal with | _ : deduplicate_log' ?l ?ks = _ |- _ => pose proof deduplicate_log'_app l [x] ks end.
repeat find_rewrite.
repeat eexists; eauto.
rewrite app_ass.
rewrite <- app_comm_cons.
eauto.
-
do_bool.
subst.
destruct (clientId_eq_dec (eClient x) client).
+
subst.
assert (id = eId x).
{
unfold applyEntry in *.
break_let.
find_inversion.
unfold getLastId in *.
simpl in *.
rewrite get_set_same in *.
find_inversion.
auto.
}
subst.
right.
unfold applyEntry in *.
break_let.
find_inversion.
exists x, (deduplicate_log' l (clientCache_to_ks (clientCache st))), [].
intuition.
*
rewrite deduplicate_log'_app.
f_equal.
simpl in *.
repeat break_match; auto.
do_bool.
find_apply_lem_hyp applyEntries_log_to_ks'.
find_apply_lem_hyp a_equiv_sym.
find_erewrite_lem assoc_a_equiv; eauto.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
break_exists.
repeat find_rewrite.
find_inversion.
omega.
*
rewrite execute_log'_app.
break_let.
simpl in *.
break_let.
simpl.
rewrite rev_app_distr.
simpl.
unfold value.
repeat f_equal.
find_apply_lem_hyp applyEntries_execute_log'.
repeat find_rewrite.
simpl in *.
repeat find_rewrite.
find_inversion.
unfold getLastId in *.
simpl in *.
rewrite get_set_same in *.
find_inversion.
auto.
+
unfold applyEntry in *.
break_let.
find_inversion.
unfold getLastId in *.
simpl in *.
rewrite get_set_diff in *; auto.
copy_eapply_prop_hyp applyEntries applyEntries; [| match goal with | H : context [id] |- _ => apply H end].
intuition.
right.
break_exists_name e; exists e.
break_exists_name xs.
exists xs.
break_exists_name ys.
break_exists.
intuition.
subst.
match goal with | _ : deduplicate_log' ?l ?ks = _ |- _ => pose proof deduplicate_log'_app l [x] ks end.
repeat find_rewrite.
repeat eexists; eauto.
rewrite app_ass.
rewrite <- app_comm_cons.
eauto.
-
do_bool.
subst.
destruct (clientId_eq_dec (eClient x) client).
+
subst.
assert (id = eId x).
{
unfold applyEntry in *.
break_let.
find_inversion.
unfold getLastId in *.
simpl in *.
rewrite get_set_same in *.
find_inversion.
auto.
}
subst.
right.
unfold applyEntry in *.
break_let.
find_inversion.
exists x, (deduplicate_log' l (clientCache_to_ks (clientCache st))), [].
intuition.
*
rewrite deduplicate_log'_app.
f_equal.
simpl in *.
repeat break_match; auto.
do_bool.
find_apply_lem_hyp applyEntries_log_to_ks'.
find_apply_lem_hyp a_equiv_sym.
find_erewrite_lem assoc_a_equiv; eauto.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
break_exists.
repeat find_rewrite.
congruence.
*
rewrite execute_log'_app.
break_let.
simpl in *.
break_let.
simpl.
rewrite rev_app_distr.
simpl.
unfold value.
repeat f_equal.
find_apply_lem_hyp applyEntries_execute_log'.
repeat find_rewrite.
simpl in *.
repeat find_rewrite.
find_inversion.
unfold getLastId in *.
simpl in *.
rewrite get_set_same in *.
find_inversion.
auto.
+
unfold applyEntry in *.
break_let.
find_inversion.
unfold getLastId in *.
simpl in *.
rewrite get_set_diff in *; auto.
copy_eapply_prop_hyp applyEntries applyEntries; [| match goal with | H : context [id] |- _ => apply H end].
intuition.
right.
break_exists_name e; exists e.
break_exists_name xs.
exists xs.
break_exists_name ys.
break_exists.
intuition.
subst.
match goal with | _ : deduplicate_log' ?l ?ks = _ |- _ => pose proof deduplicate_log'_app l [x] ks end.
repeat find_rewrite.
repeat eexists; eauto.
rewrite app_ass.
rewrite <- app_comm_cons.
eauto.
