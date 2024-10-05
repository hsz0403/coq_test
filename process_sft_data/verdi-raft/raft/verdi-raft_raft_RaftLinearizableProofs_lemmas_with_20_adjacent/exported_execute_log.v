Require Import Sumbool.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.TraceUtil.
Require Import VerdiRaft.Linearizability.
Require Import VerdiRaft.OutputImpliesAppliedInterface.
Require Import VerdiRaft.AppliedImpliesInputInterface.
Require Import VerdiRaft.CausalOrderPreservedInterface.
Require Import VerdiRaft.OutputCorrectInterface.
Require Import VerdiRaft.InputBeforeOutputInterface.
Require Import VerdiRaft.OutputGreatestIdInterface.
Section RaftLinearizableProofs.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {oiai : output_implies_applied_interface}.
Context {aiii : applied_implies_input_interface}.
Context {copi : causal_order_preserved_interface}.
Context {iboi : input_before_output_interface}.
Context {oci : output_correct_interface}.
Context {ogii : output_greatest_id_interface}.
Definition op_eq_dec : forall x y : op key, {x = y} + {x <> y}.
Proof using.
decide equality; auto using key_eq_dec.
Fixpoint import (tr : list (name * (raft_input + list raft_output))) : list (op key) := match tr with | [] => [] | (_, (inl (ClientRequest c id cmd))) :: xs => I (c, id) :: remove op_eq_dec (I (c, id)) (import xs) | (_, (inr l)) :: xs => let os := dedup op_eq_dec (filterMap (fun x => match x with | ClientResponse c id cmd => Some (O (c, id)) | _ => None end) l) in os ++ remove_all op_eq_dec os (import xs) | _ :: xs => import xs end.
Inductive exported (env_i : key -> option input) (env_o : key -> option output) : list (IR key) -> list (input * output) -> Prop := | exported_nil : exported env_i env_o nil nil | exported_IO : forall k i o l tr, env_i k = Some i -> env_o k = Some o -> exported env_i env_o l tr -> exported env_i env_o (IRI k :: IRO k :: l) ((i, o) :: tr) | exported_IU : forall k i o l tr, env_i k = Some i -> exported env_i env_o l tr -> exported env_i env_o (IRI k :: IRU k :: l) ((i, o) :: tr).
Fixpoint get_input (tr : list (name * (raft_input + list raft_output))) (k : key) : option input := match tr with | [] => None | (_, (inl (ClientRequest c id cmd))) :: xs => if (sumbool_and _ _ _ _ (clientId_eq_dec c (fst k)) (eq_nat_dec id (snd k))) then Some cmd else get_input xs k | _ :: xs => get_input xs k end.
Fixpoint get_output' (os : list raft_output) (k : key) : option output := match os with | [] => None | ClientResponse c id o :: xs => if (sumbool_and _ _ _ _ (clientId_eq_dec c (fst k)) (eq_nat_dec id (snd k))) then Some o else get_output' xs k | _ :: xs => get_output' xs k end.
Fixpoint get_output (tr : list (name * (raft_input + list raft_output))) (k : key) : option output := match tr with | [] => None | (_, (inr os)) :: xs => (match get_output' os k with | Some o => Some o | None => get_output xs k end) | _ :: xs => get_output xs k end.
Fixpoint log_to_IR (env_o : key -> option output) (log : list entry) {struct log} : list (IR key) := match log with | [] => [] | mkEntry h client id index term input :: log' => (match env_o (client, id) with | None => [IRI (client, id); IRU (client, id)] | Some _ => [IRI (client, id); IRO (client, id)] end) ++ log_to_IR env_o log' end.
Hint Constructors exported : core.
Definition input_correct (tr : list (name * (raft_input + list raft_output))) : Prop := (forall client id i i' h h', In (h, inl (ClientRequest client id i)) tr -> In (h', inl (ClientRequest client id i')) tr -> i = i').
End RaftLinearizableProofs.

Lemma has_key_true_same_client : forall c i e, has_key c i e = true -> eClient e = c.
Proof using.
unfold has_key.
intros.
destruct e.
simpl.
do_bool.
break_and.
do_bool.
Admitted.

Lemma has_key_true_same_id : forall c i e, has_key c i e = true -> eId e = i.
Proof using.
unfold has_key.
intros.
destruct e.
simpl.
do_bool.
intuition.
do_bool.
Admitted.

Lemma has_key_true_elim : forall c i e, has_key c i e = true -> eClient e = c /\ eId e = i.
Proof using.
Admitted.

Lemma has_key_false_elim : forall c i e, has_key c i e = false -> eClient e <> c \/ eId e <> i.
Proof using.
unfold has_key.
intros.
destruct e.
simpl.
do_bool.
intuition (do_bool; auto).
break_if; try congruence.
Admitted.

Lemma before_func_deduplicate' : forall l k k' ks, before_func (has_key (fst k) (snd k)) (has_key (fst k') (snd k')) l -> (forall id', before_func (has_key (fst k) id') (has_key (fst k) (snd k)) l -> id' <= snd k) -> (forall i, assoc clientId_eq_dec ks (fst k) = Some i -> i < snd k) -> before_func (has_key (fst k) (snd k)) (has_key (fst k') (snd k')) (deduplicate_log' l ks).
Proof using.
induction l; simpl; intros.
-
intuition.
-
intuition.
+
repeat break_match; simpl; auto.
do_bool.
find_apply_lem_hyp has_key_true_elim.
break_and.
repeat find_rewrite.
assert (n < snd k) by auto.
omega.
+
repeat break_match; simpl.
*
{
destruct (has_key (fst k) (snd k) a) eqn:?; auto.
right.
intuition.
apply IHl; auto.
do_bool.
intros.
destruct (clientId_eq_dec (eClient a) (fst k)).
-
repeat find_rewrite.
rewrite get_set_same in *.
find_inversion.
repeat match goal with | H : context [ has_key (fst k')] |- _ => clear H end.
find_apply_lem_hyp has_key_false_elim.
intuition; try congruence.
assert (has_key (fst k) (eId a) a = true) by eauto using has_key_intro'.
assert (eId a <= snd k) by auto.
omega.
-
rewrite get_set_diff in * by auto.
auto.
}
*
do_bool.
apply IHl; auto.
intros.
{
destruct (has_key (fst k) (snd k) a) eqn:?; auto.
find_apply_lem_hyp has_key_true_elim.
break_and.
repeat find_rewrite.
assert (n < snd k) by auto.
omega.
}
*
{
destruct (has_key (fst k) (snd k) a) eqn:?; auto.
right.
intuition.
apply IHl; auto.
do_bool.
intros.
destruct (clientId_eq_dec (eClient a) (fst k)).
-
repeat find_rewrite.
rewrite get_set_same in *.
find_inversion.
repeat match goal with | H : context [ has_key (fst k')] |- _ => clear H end.
find_apply_lem_hyp has_key_false_elim.
intuition; try congruence.
assert (has_key (fst k) (eId a) a = true) by eauto using has_key_intro'.
assert (eId a <= snd k) by auto.
omega.
-
rewrite get_set_diff in * by auto.
auto.
Admitted.

Lemma before_func_deduplicate : forall k k' l, before_func (has_key (fst k) (snd k)) (has_key (fst k') (snd k')) l -> (forall id', before_func (has_key (fst k) id') (has_key (fst k) (snd k)) l -> id' <= snd k) -> before_func (has_key (fst k) (snd k)) (has_key (fst k') (snd k')) (deduplicate_log l).
Proof using.
intros.
apply before_func_deduplicate'; auto.
simpl.
intros.
Admitted.

Lemma entries_ordered_before_log_to_IR : forall k k' net failed tr, step_failure_star step_failure_init (failed, net) tr -> In (O k) (import tr) -> k <> k' -> entries_ordered (fst k) (snd k) (fst k') (snd k') net -> before (IRO k) (IRI k') (log_to_IR (get_output tr) (deduplicate_log (applied_entries (nwState net)))).
Proof using ogii.
intros.
unfold entries_ordered in *.
remember (applied_entries (nwState net)) as l.
find_apply_lem_hyp before_func_deduplicate.
{
remember (deduplicate_log l) as l'; clear Heql'.
clear Heql.
clear l.
rename l' into l.
induction l; simpl in *; intuition.
-
repeat break_match; subst; simpl in *; break_if; try discriminate; repeat (do_bool; intuition).
+
destruct k; simpl in *; subst.
right.
intuition.
find_inversion.
simpl in *.
intuition.
+
exfalso.
destruct k; subst; simpl in *.
find_apply_lem_hyp import_get_output.
break_exists.
congruence.
-
repeat break_match; subst; simpl in *; repeat (do_bool; intuition); try break_if; try congruence.
+
right.
destruct k'.
simpl in *.
intuition; try congruence.
destruct (key_eq_dec k (eClient, eId)); subst; intuition.
right.
intuition; congruence.
+
right.
destruct k'.
simpl in *.
intuition; try congruence.
destruct (key_eq_dec k (eClient, eId)); subst; intuition.
right.
intuition; congruence.
+
right.
intuition; [find_inversion; simpl in *; intuition|].
right.
intuition.
congruence.
+
right.
intuition; [find_inversion; simpl in *; intuition|].
right.
intuition.
congruence.
}
{
intros.
subst.
eapply output_greatest_id with (client := fst k) (id := snd k) in H.
-
intros.
unfold greatest_id_for_client in *.
destruct (le_lt_dec id' (snd k)); auto.
find_copy_apply_hyp_hyp.
exfalso.
eapply before_func_antisymmetric; try eassumption.
unfold has_key.
intros.
destruct x.
do_bool.
intuition.
do_bool.
subst.
omega.
-
red.
find_apply_lem_hyp in_import_in_trace_O.
break_exists_exists.
intuition.
Admitted.

Lemma input_before_output_import : forall tr k, before_func (is_input_with_key (fst k) (snd k)) (is_output_with_key (fst k) (snd k)) tr -> before (I k) (O k) (import tr).
Proof using.
intros; induction tr; simpl in *; intuition.
-
repeat break_match; subst; simpl in *; intuition; try congruence.
break_if; repeat (do_bool; intuition); try congruence.
destruct k; subst; simpl in *; intuition.
-
repeat break_match; subst; simpl in *; intuition; try congruence.
+
destruct k.
match goal with | |- context [ I (?x, ?y) = I (?x', ?y') ] => destruct (op_eq_dec (I (x, y)) (I (x', y'))) end; subst; intuition.
right.
intuition; try congruence.
apply before_remove_if; intuition.
+
break_if; try congruence.
apply before_app_if; [apply before_remove_all_if|]; auto.
*
intuition.
find_apply_lem_hyp in_dedup_was_in.
find_apply_lem_hyp In_filterMap.
break_exists.
break_match; intuition; congruence.
*
intuition.
match goal with | H : _ -> False |- False => apply H end.
find_apply_lem_hyp in_dedup_was_in.
find_apply_lem_hyp In_filterMap.
break_exists.
intuition.
break_match; try congruence.
find_inversion.
unfold key_in_output_list.
simpl.
Admitted.

Lemma I_before_O : forall failed net tr k, step_failure_star step_failure_init (failed, net) tr -> In (O k) (import tr) -> before (I k) (O k) (import tr).
Proof using iboi.
intros.
find_apply_lem_hyp in_import_in_trace_O.
find_eapply_lem_hyp output_implies_input_before_output; eauto.
Admitted.

Lemma get_IR_input_keys_log_to_IR : forall l env_o, get_IR_input_keys key (log_to_IR env_o l) = map (fun e => (eClient e, eId e)) l.
Proof using.
intros.
induction l; simpl in *; intuition.
Admitted.

Lemma get_IR_output_keys_log_to_IR : forall l env_o, get_IR_output_keys key (log_to_IR env_o l) = map (fun e => (eClient e, eId e)) l.
Proof using.
intros.
induction l; simpl in *; intuition.
Admitted.

Lemma deduplicate_log'_ks : forall l ks e id, In e (deduplicate_log' l ks) -> assoc clientId_eq_dec ks (eClient e) = Some id -> id < (eId e).
Proof using.
induction l; intros; simpl in *; intuition.
repeat break_match; simpl in *; do_bool; intuition; subst; eauto; repeat find_rewrite; repeat find_inversion; intuition.
-
destruct (clientId_eq_dec (eClient e) (eClient a)); repeat find_rewrite.
*
find_injection.
eapply IHl with (id := eId a) in H1; try omega.
repeat find_rewrite.
eauto using get_set_same.
*
eapply IHl with (id := id) in H1; try omega.
rewrite get_set_diff; auto.
-
congruence.
-
destruct (clientId_eq_dec (eClient e) (eClient a)); repeat find_rewrite.
*
congruence.
*
eapply IHl with (id := id) in H1; try omega.
Admitted.

Lemma NoDup_deduplicate_log' : forall l ks, NoDup (map (fun e => (eClient e, eId e)) (deduplicate_log' l ks)).
Proof using.
induction l; intros.
-
simpl in *.
constructor.
-
simpl in *.
repeat break_match; eauto.
+
simpl in *.
constructor; eauto.
intuition.
do_in_map.
find_inversion.
eapply deduplicate_log'_ks with (id := eId a) in H0; try omega.
repeat find_rewrite.
rewrite get_set_same.
auto.
+
simpl in *.
constructor; eauto.
intuition.
do_in_map.
find_inversion.
eapply deduplicate_log'_ks with (id := eId a) in H0; try omega.
repeat find_rewrite.
rewrite get_set_same.
Admitted.

Lemma NoDup_deduplicate_log : forall l, NoDup (map (fun e => (eClient e, eId e)) (deduplicate_log l)).
Proof using.
Admitted.

Lemma NoDup_input_log : forall l env_o, NoDup (get_IR_input_keys key (log_to_IR env_o (deduplicate_log l))).
Proof using.
intros.
rewrite get_IR_input_keys_log_to_IR.
Admitted.

Lemma NoDup_output_log : forall l env_o, NoDup (get_IR_output_keys key (log_to_IR env_o (deduplicate_log l))).
Proof using.
intros.
rewrite get_IR_output_keys_log_to_IR.
Admitted.

Lemma exported_snoc_IO : forall env_i env_o ir tr i o k, exported env_i env_o ir tr -> env_i k = Some i -> env_o k = Some o -> exported env_i env_o (ir ++ [IRI k; IRO k]) (tr ++ [(i, o)]).
Proof using.
Admitted.

Lemma exported_snoc_IU : forall env_i env_o ir tr i k o, exported env_i env_o ir tr -> env_i k = Some i -> env_o k = None -> exported env_i env_o (ir ++ [IRI k; IRU k]) (tr ++ [(i, o)]).
Proof using.
Admitted.

Lemma log_to_IR_app : forall xs ys env, log_to_IR env (xs ++ ys) = log_to_IR env xs ++ log_to_IR env ys.
Proof using.
induction xs; intros; simpl; intuition.
Admitted.

Lemma exported_execute_log' : forall env_i env_o l es tr st, (forall e, In e l -> env_i (eClient e, eId e) = Some (eInput e)) -> (forall xs ys e tr' st' o o0 st'', l = xs ++ e :: ys -> execute_log' xs st tr = (tr', st') -> handler (eInput e) st' = (o, st'') -> env_o (eClient e, eId e) = Some o0 -> o = o0) -> execute_log es = (tr, st) -> exported env_i env_o (log_to_IR env_o es) tr -> exported env_i env_o (log_to_IR env_o (es ++ l)) (fst (execute_log' l st tr)).
Proof using.
induction l using rev_ind; intros; simpl in *.
-
rewrite app_nil_r.
auto.
-
rewrite execute_log'_app.
simpl.
repeat break_let.
simpl.
eapply_prop_hyp execute_log execute_log; auto.
+
find_rewrite.
simpl in *.
rewrite <- app_ass.
rewrite log_to_IR_app.
simpl.
specialize (H x).
conclude_using eauto.
specialize (H0 l [] x l0 d).
break_match; subst; simpl in *.
rewrite app_nil_r.
break_match.
*
specialize (H0 o o0 d0).
repeat concludes.
apply exported_snoc_IO; congruence.
*
apply exported_snoc_IU; auto.
+
intros.
apply H.
intuition.
+
intros.
subst.
eapply H0 with (ys0 := ys ++ [x]).
rewrite app_ass.
simpl.
eauto.
eauto.
eauto.
Admitted.

Lemma in_input_trace_get_input : forall tr e, input_correct tr -> in_input_trace (eClient e) (eId e) (eInput e) tr -> get_input tr (eClient e, eId e) = Some (eInput e).
Proof using.
unfold in_input_trace, input_correct.
Admitted.

Lemma get_output_in_output_trace : forall tr client id o, get_output tr (client, id) = Some o -> in_output_trace client id o tr.
Proof using.
intros.
induction tr; simpl in *; try congruence.
repeat break_let.
subst.
repeat break_match; simpl in *; intuition; subst; try solve [unfold in_output_trace in *;break_exists_exists; intuition].
find_inversion.
find_apply_lem_hyp get_output'_In.
Admitted.

Lemma deduplicate_partition : forall l xs e ys xs' e' ys', deduplicate_log l = xs ++ e :: ys -> deduplicate_log l = xs' ++ e' :: ys' -> eClient e = eClient e' -> eId e = eId e' -> xs = xs'.
Proof using.
intros.
eapply NoDup_map_partition.
-
apply NoDup_deduplicate_log.
-
eauto.
-
eauto.
-
simpl.
Admitted.

Lemma applied_entries_applied_implies_input_state : forall net e, In e (applied_entries (nwState net)) -> applied_implies_input_state (eClient e) (eId e) (eInput e) net.
Proof using.
intros.
red.
exists e.
intuition.
-
red.
auto.
-
unfold applied_entries in *.
break_match.
+
find_apply_lem_hyp in_rev.
find_apply_lem_hyp removeAfterIndex_in.
eauto.
+
simpl in *.
Admitted.

Theorem raft_linearizable' : forall failed net tr, input_correct tr -> step_failure_star step_failure_init (failed, net) tr -> exists l tr1 st, equivalent _ (import tr) l /\ exported (get_input tr) (get_output tr) l tr1 /\ step_1_star init st tr1.
Proof using ogii oci iboi copi aiii oiai.
intros.
exists (log_to_IR (get_output tr) (deduplicate_log (applied_entries (nwState net)))).
exists (fst (execute_log (deduplicate_log (applied_entries (nwState net))))).
exists (snd (execute_log (deduplicate_log (applied_entries (nwState net))))).
intuition eauto using execute_log_correct.
-
eapply equivalent_intro; eauto using log_to_IR_good_trace, key_eq_dec.
+
intros.
find_copy_apply_lem_hyp in_import_in_trace_O.
find_eapply_lem_hyp output_implies_applied; eauto.
unfold in_applied_entries in *.
break_exists.
intuition.
destruct k; simpl in *.
find_apply_lem_hyp deduplicate_log_In.
*
break_exists.
intuition.
repeat find_rewrite.
eapply in_applied_entries_in_IR; eauto.
apply import_get_output.
auto.
*
{
eapply output_greatest_id with (client := eClient x) (id := eId x) in H0.
-
intros.
unfold greatest_id_for_client in *.
subst.
destruct (le_lt_dec id' (eId x)); auto.
find_copy_apply_hyp_hyp.
exfalso.
eapply before_func_antisymmetric; try eassumption.
unfold has_key.
intros.
destruct x0.
do_bool.
intuition.
do_bool.
subst.
omega.
-
red.
find_apply_lem_hyp in_import_in_trace_O.
break_exists_exists.
intuition.
red.
simpl in *.
subst.
auto.
}
+
intros.
find_apply_lem_hyp IRO_in_IR_in_log.
break_exists.
break_and.
eapply get_output_import_O; eauto.
+
intros.
find_apply_lem_hyp IRU_in_IR_in_log.
break_exists.
break_and.
destruct k as [c id].
find_apply_lem_hyp deduplicate_log_In_if.
find_eapply_lem_hyp applied_implies_input; eauto.
*
unfold in_input_trace in *.
break_exists.
eauto using trace_I_in_import.
*
simpl in *.
subst.
auto using applied_entries_applied_implies_input_state.
+
intros.
assert (k <> k').
*
intuition.
subst.
find_copy_apply_lem_hyp before_In.
find_eapply_lem_hyp I_before_O; eauto.
find_eapply_lem_hyp before_antisymmetric; auto.
congruence.
*
eauto using before_In, before_import_output_before_input, causal_order_preserved, entries_ordered_before_log_to_IR.
+
intros.
eauto using I_before_O.
+
intros.
find_apply_lem_hyp IRU_in_IR_in_log.
break_exists.
break_and.
intro.
find_apply_lem_hyp import_get_output.
break_exists.
congruence.
+
apply NoDup_input_import.
+
apply NoDup_input_log.
+
apply NoDup_output_import.
+
apply NoDup_output_log.
-
apply exported_execute_log.
+
intros.
find_apply_lem_hyp deduplicate_log_In_if.
apply in_input_trace_get_input.
*
auto.
*
eapply applied_implies_input; eauto.
auto using applied_entries_applied_implies_input_state.
+
intros.
find_apply_lem_hyp get_output_in_output_trace.
find_eapply_lem_hyp output_correct_invariant; eauto.
unfold output_correct in *.
break_exists.
intuition.
find_eapply_lem_hyp deduplicate_partition; eauto.
subst.
repeat find_rewrite.
find_apply_lem_hyp app_inv_head.
find_inversion.
unfold execute_log in *.
find_rewrite_lem execute_log'_app.
simpl in *.
repeat break_let.
find_inversion.
find_inversion.
rewrite rev_app_distr in *.
simpl in *.
find_injection.
find_injection.
unfold value in *.
find_inversion.
repeat find_rewrite.
find_inversion.
Admitted.

Lemma exported_execute_log : forall env_i env_o l, (forall e, In e l -> env_i (eClient e, eId e) = Some (eInput e)) -> (forall xs ys e tr' st' o o0 st'', l = xs ++ e :: ys -> execute_log xs = (tr', st') -> handler (eInput e) st' = (o, st'') -> env_o (eClient e, eId e) = Some o0 -> o = o0) -> exported env_i env_o (log_to_IR env_o l) (fst (execute_log l)).
Proof using.
intros.
unfold execute_log.
change (log_to_IR env_o l) with (log_to_IR env_o ([] ++ l)).
eapply exported_execute_log'; eauto.
