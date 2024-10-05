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

Lemma snd_execute_log' : forall l st o o', snd (execute_log' l st o) = snd (execute_log' l st o').
Proof using.
Admitted.

Lemma snd_execute_log'_nil : forall l st o, snd (execute_log' l st o) = snd (execute_log' l st []).
Proof using.
Admitted.

Lemma clientCache_to_ks_assoc : forall c client id, assoc clientId_eq_dec (clientCache_to_ks c) client = Some id -> exists o, assoc clientId_eq_dec c client = Some (id, o).
Proof using.
induction c; intros; simpl in *; try congruence.
break_if; eauto.
-
subst.
find_inversion.
break_let.
subst.
simpl in *.
break_if; try congruence.
destruct p.
simpl in *.
eauto.
-
break_let; subst; simpl in *.
break_if; try congruence.
Admitted.

Lemma clientCache_to_ks_assoc_none : forall c client, assoc clientId_eq_dec (clientCache_to_ks c) client = None -> assoc clientId_eq_dec c client = None.
Proof using.
induction c; intros; simpl in *; try congruence.
break_if; eauto; try congruence.
-
break_let; subst; simpl in *.
break_if; try congruence.
Admitted.

Lemma clientCache_to_ks_assoc_getLastId_none : forall st client, assoc clientId_eq_dec (clientCache_to_ks (clientCache st)) client = None -> getLastId st client = None.
Proof using.
Admitted.

Lemma cacheApplyEntry_stateMachine_apply : forall st e os st' id o o' d, cacheApplyEntry st e = (os, st') -> getLastId st (eClient e) = Some (id, o) -> id < eId e -> handler (eInput e) (stateMachine st) = (o', d) -> stateMachine st' = d.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma cacheApplyEntry_cache_apply : forall st e os st' id o o' d, cacheApplyEntry st e = (os, st') -> getLastId st (eClient e) = Some (id, o) -> id < eId e -> handler (eInput e) (stateMachine st) = (o', d) -> assoc_set clientId_eq_dec (clientCache st) (eClient e) (eId e, o') = clientCache st'.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma cacheApplyEntry_stateMachine_apply_none : forall st e os st' o' d, cacheApplyEntry st e = (os, st') -> getLastId st (eClient e) = None -> handler (eInput e) (stateMachine st) = (o', d) -> stateMachine st' = d.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma cacheApplyEntry_cache_apply_none : forall st e os st' o' d, cacheApplyEntry st e = (os, st') -> getLastId st (eClient e) = None -> handler (eInput e) (stateMachine st) = (o', d) -> assoc_set clientId_eq_dec (clientCache st) (eClient e) (eId e, o') = clientCache st'.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma cacheApplyEntry_stateMachine_no_apply : forall st e os st' id o, cacheApplyEntry st e = (os, st') -> getLastId st (eClient e) = Some (id, o) -> eId e <= id -> stateMachine st' = stateMachine st.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma cacheApplyEntry_cache_no_apply : forall st e os st' id o, cacheApplyEntry st e = (os, st') -> getLastId st (eClient e) = Some (id, o) -> eId e <= id -> clientCache st = clientCache st'.
Proof using.
intros.
unfold cacheApplyEntry, applyEntry in *.
Admitted.

Lemma clientCache_to_ks_assoc_set : forall c client id o, assoc_set clientId_eq_dec (clientCache_to_ks c) client id = clientCache_to_ks (assoc_set clientId_eq_dec c client (id, o)).
Proof using.
induction c; intros; simpl in *; intuition.
simpl.
break_if; simpl in *; eauto.
f_equal.
Admitted.

Lemma applyEntries_execute_log' : forall l h st os st', applyEntries h st l = (os, st') -> stateMachine st' = (snd (execute_log' (deduplicate_log' l (clientCache_to_ks (clientCache st))) (stateMachine st) [])).
Proof using.
induction l; intros; simpl in *; intuition.
-
find_inversion.
auto.
-
repeat break_let.
find_inversion.
repeat break_match; simpl in *.
+
break_let.
rewrite snd_execute_log'_nil.
find_apply_hyp_hyp.
do_bool.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
break_exists.
find_copy_eapply_lem_hyp cacheApplyEntry_stateMachine_apply; [|eauto|idtac|]; eauto.
subst.
find_eapply_lem_hyp cacheApplyEntry_cache_apply; eauto.
erewrite clientCache_to_ks_assoc_set.
rewrite Heqp1.
eauto.
+
do_bool.
find_apply_hyp_hyp.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
break_exists.
break_exists.
find_copy_eapply_lem_hyp cacheApplyEntry_stateMachine_no_apply; eauto.
find_eapply_lem_hyp cacheApplyEntry_cache_no_apply; eauto.
repeat find_rewrite.
auto.
+
break_let.
rewrite snd_execute_log'_nil.
find_apply_hyp_hyp.
do_bool.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId_none.
break_exists.
find_copy_eapply_lem_hyp cacheApplyEntry_stateMachine_apply_none; eauto.
subst.
find_eapply_lem_hyp cacheApplyEntry_cache_apply_none; eauto.
erewrite clientCache_to_ks_assoc_set.
rewrite Heqp1.
Admitted.

Lemma clientCache_to_ks_assoc_getLastId : forall st client id, assoc clientId_eq_dec (clientCache_to_ks (clientCache st)) client = Some id -> exists o, getLastId st client = Some (id, o).
Proof using.
eauto using clientCache_to_ks_assoc.
