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

Lemma assoc_set_log_to_ks'_le: forall (l : list entry) (ks : list (clientId * nat)) c i, assoc_default clientId_eq_dec (log_to_ks' l ks) c 0 <= i -> a_equiv clientId_eq_dec (assoc_set clientId_eq_dec (log_to_ks' l ks) c i) (log_to_ks' l (assoc_set clientId_eq_dec ks c i)).
Proof using.
induction l; intros; simpl in *; eauto using a_equiv_refl.
repeat break_if; simpl in *; eauto.
-
do_bool.
destruct (clientId_eq_dec (eClient a) c); subst.
+
repeat rewrite assoc_set_assoc_set_same.
find_rewrite_lem assoc_default_assoc_set.
assert (i = eId a) by (eapply le_antisym; auto; eapply le_trans; [|eauto]; eauto using log_to_ks'_assoc_default_ks).
subst.
find_apply_hyp_hyp.
find_rewrite_lem assoc_set_assoc_set_same.
auto.
+
eapply a_equiv_sym.
eapply a_equiv_trans; [eapply log_to_ks'_a_equiv; eapply assoc_set_assoc_set_diff; auto|].
eapply a_equiv_sym.
eauto.
-
do_bool.
destruct (clientId_eq_dec (eClient a) c); subst.
+
find_rewrite_lem assoc_default_assoc_set.
find_apply_hyp_hyp.
find_rewrite_lem assoc_set_assoc_set_same.
auto.
+
rewrite assoc_default_assoc_set_diff in *; auto.
omega.
-
do_bool.
destruct (clientId_eq_dec (eClient a) c); subst.
+
find_rewrite_lem assoc_default_assoc_set.
rewrite assoc_set_assoc_set_same.
assert (i = eId a); subst; eauto.
eapply le_antisym; eauto.
eapply le_trans; [|eauto].
eapply le_trans; [|eapply log_to_ks'_assoc_default_assoc_default_le].
omega.
+
rewrite assoc_default_assoc_set_diff in *; auto.
omega.
