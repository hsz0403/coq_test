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

Lemma client_cache_correct_do_generic_server : raft_net_invariant_do_generic_server' client_cache_correct.
Proof using lmi smsi misi si.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
repeat find_rewrite.
find_apply_lem_hyp doGenericServer_spec.
intuition; repeat find_rewrite; eauto.
get_invariant_pre logs_sorted_invariant.
unfold logs_sorted in *.
intuition.
erewrite removeAfterIndex_app; eauto.
break_exists.
intuition.
find_higher_order_rewrite.
find_eapply_lem_hyp applyEntries_execute_log'_cache; eauto.
intuition.
-
find_apply_hyp_hyp.
rewrite rev_app_distr.
eauto using output_correct_monotonic.
-
unfold output_correct.
break_exists.
intuition.
rewrite rev_app_distr.
unfold deduplicate_log.
rewrite deduplicate_log'_app.
match goal with | _ : context [execute_log' ?x ?y] |- _ => destruct (execute_log' x y) eqn:? end.
simpl in *.
match goal with | [ H : deduplicate_log' _ _ = ?xs ++ ?e :: ?ys |- context [?l ++ deduplicate_log' _ _] ] => (exists (l ++ xs), e, ys) end.
unfold execute_log.
repeat rewrite app_ass.
rewrite execute_log'_app.
break_let.
get_invariant_pre state_machine_log_invariant.
unfold state_machine_log in *.
repeat find_higher_order_rewrite.
unfold execute_log, deduplicate_log in *.
repeat find_rewrite.
simpl in *.
match goal with | [ H : execute_log' (_ ++ _) _ _ = (?tr, ?st) |- context [execute_log' _ _ ?tr'] ] => (exists (tr' ++ tr), st) end.
intuition.
+
f_equal.
repeat find_reverse_rewrite.
match goal with | H : deduplicate_log' _ _ = _ ++ _ :: _ |- _ => clear H end.
match goal with | |- _ ?l _ = _ ?l' _ => assert (l = l') by (f_equal; apply filter_fun_ext_eq; intros; repeat find_rewrite; rewrite <- Bool.andb_true_l at 1; f_equal; symmetry; apply Nat.ltb_lt; find_apply_lem_hyp findGtIndex_necessary; intuition) end.
repeat find_rewrite.
apply deduplicate_log'_a_equiv.
apply a_equiv_sym.
apply client_cache_keys_correct_invariant; auto.
+
eauto using execute_log'_trace_nil.
+
rewrite rev_app_distr.
erewrite hd_error_Some_app; eauto.
