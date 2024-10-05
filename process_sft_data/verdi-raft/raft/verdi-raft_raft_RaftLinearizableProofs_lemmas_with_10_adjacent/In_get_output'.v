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

Lemma has_key_intro' : forall e c i, eClient e = c -> eId e = i -> has_key c i e = true.
Proof using.
intros.
subst.
Admitted.

Lemma has_key_different_id_false : forall e e', eId e <> eId e' -> has_key (eClient e) (eId e) e' = false.
Proof using.
unfold has_key.
intros.
destruct e'.
simpl in *.
do_bool.
right.
do_bool.
Admitted.

Lemma has_key_different_client_false : forall e e', eClient e <> eClient e' -> has_key (eClient e) (eId e) e' = false.
Proof using.
unfold has_key.
intros.
destruct e'.
simpl in *.
do_bool.
left.
Admitted.

Lemma deduplicate_log'_In : forall l e, In e l -> forall ks, (forall i, assoc clientId_eq_dec ks (eClient e) = Some i -> i < eId e) -> (forall id', before_func (has_key (eClient e) id') (has_key (eClient e) (eId e)) l -> id' <= eId e) -> (exists e', eClient e' = eClient e /\ eId e' = eId e /\ In e' (deduplicate_log' l ks)).
Proof using.
induction l; simpl.
-
intuition.
-
intros.
repeat break_match; intuition; subst; simpl in *; intuition eauto.
+
do_bool.
destruct (clientId_eq_dec (eClient e) (eClient a)).
*
assert (eId a <= eId e).
{
repeat find_rewrite.
auto using has_key_intro.
}
{
find_apply_lem_hyp le_lt_or_eq.
break_or_hyp.
-
specialize (IHl _ ltac:(eauto)).
match goal with | [ |- context [deduplicate_log' _ ?ks] ] => specialize (IHl ks) end.
forward IHl.
{
intuition.
repeat find_rewrite.
rewrite get_set_same in *.
find_injection.
auto.
}
concludes.
forward IHl.
{
intuition auto using has_key_different_id_false with *.
}
concludes.
break_exists_exists.
intuition.
-
eauto.
}
*
specialize (IHl _ ltac:(eauto)).
match goal with | [ |- context [deduplicate_log' _ ?ks] ] => specialize (IHl ks) end.
forward IHl.
{
intuition.
repeat find_rewrite.
rewrite get_set_diff in * by auto.
auto.
}
concludes.
forward IHl.
{
intuition auto using has_key_different_client_false with *.
}
concludes.
break_exists_exists.
intuition.
+
do_bool.
assert (n < eId e) by auto.
omega.
+
do_bool.
apply IHl; auto.
intros.
destruct (clientId_eq_dec (eClient e) (eClient a)).
*
assert (eId e <> eId a).
{
intro.
repeat find_rewrite.
assert (n < eId a) by auto.
omega.
}
intuition auto using has_key_different_id_false with *.
*
intuition auto using has_key_different_client_false with *.
+
destruct (clientId_eq_dec (eClient e) (eClient a)).
*
assert (eId a <= eId e).
{
repeat find_rewrite.
auto using has_key_intro.
}
{
find_apply_lem_hyp le_lt_or_eq.
break_or_hyp.
-
specialize (IHl _ ltac:(eauto)).
match goal with | [ |- context [deduplicate_log' _ ?ks] ] => specialize (IHl ks) end.
forward IHl.
{
intuition.
repeat find_rewrite.
rewrite get_set_same in *.
find_injection.
auto.
}
concludes.
forward IHl.
{
intuition auto using has_key_different_id_false with *.
}
concludes.
break_exists_exists.
intuition.
-
eauto.
}
*
specialize (IHl _ ltac:(eauto)).
match goal with | [ |- context [deduplicate_log' _ ?ks] ] => specialize (IHl ks) end.
forward IHl.
{
intuition.
repeat find_rewrite.
rewrite get_set_diff in * by auto.
auto.
}
concludes.
forward IHl.
{
intuition auto using has_key_different_client_false with *.
}
concludes.
break_exists_exists.
Admitted.

Lemma deduplicate_log_In : forall l e, In e l -> (forall id', before_func (has_key (eClient e) id') (has_key (eClient e) (eId e)) l -> id' <= eId e) -> exists e', eClient e' = eClient e /\ eId e' = eId e /\ In e' (deduplicate_log l).
Proof using.
unfold deduplicate_log'.
intros.
Admitted.

Lemma deduplicate_log_In_if : forall l e, In e (deduplicate_log l) -> In e l.
Proof using.
Admitted.

Lemma log_to_IR_good_trace : forall env_o log, good_trace _ (log_to_IR env_o log).
Proof using.
intros.
induction log; simpl in *; auto.
-
Admitted.

Lemma in_import_in_trace_O : forall tr k, In (O k) (import tr) -> exists os h, In (h, inr os) tr /\ exists o, In (ClientResponse (fst k) (snd k) o) os.
Proof using.
induction tr; intros; simpl in *; intuition.
repeat break_match; subst; intuition.
-
find_apply_hyp_hyp.
break_exists_exists.
intuition.
-
simpl in *.
intuition; try congruence.
find_apply_lem_hyp in_remove.
find_apply_hyp_hyp.
break_exists_exists.
intuition.
-
do_in_app.
intuition.
+
find_apply_lem_hyp in_dedup_was_in.
find_apply_lem_hyp In_filterMap.
break_exists.
intuition.
break_match; try congruence.
find_inversion.
repeat eexists; intuition eauto.
+
find_apply_lem_hyp in_remove_all_was_in.
find_apply_hyp_hyp.
break_exists_exists.
Admitted.

Lemma in_import_in_trace_I : forall tr k, In (I k) (import tr) -> exists h i, In (h, inl (ClientRequest (fst k) (snd k) i)) tr.
Proof using.
induction tr; intros; simpl in *; intuition.
repeat break_match; subst.
-
find_apply_hyp_hyp.
break_exists.
eauto 10.
-
simpl in *.
intuition.
+
find_inversion.
simpl.
eauto 10.
+
find_apply_lem_hyp in_remove.
find_apply_hyp_hyp.
break_exists.
eauto 10.
-
do_in_app.
intuition.
+
find_apply_lem_hyp in_dedup_was_in.
find_eapply_lem_hyp In_filterMap.
break_exists.
break_and.
break_match; discriminate.
+
find_eapply_lem_hyp in_remove_all_was_in.
find_apply_hyp_hyp.
break_exists.
Admitted.

Lemma in_applied_entries_in_IR : forall log e client id env, eClient e = client -> eId e = id -> In e log -> (exists o, env (client, id) = Some o) -> In (IRO (client, id)) (log_to_IR env log).
Proof using.
intros.
induction log; simpl in *; intuition.
-
subst.
break_exists.
repeat break_match; intuition.
simpl in *.
subst.
congruence.
-
Admitted.

Theorem import_get_output : forall tr k, In (O k) (import tr) -> exists o, get_output tr k = Some o.
Proof using.
intros.
induction tr; simpl in *; intuition.
repeat break_match; intuition; subst; simpl in *; intuition; try congruence; try do_in_app; intuition eauto.
-
find_apply_lem_hyp in_remove; auto.
-
find_apply_lem_hyp in_dedup_was_in; auto.
find_apply_lem_hyp In_filterMap.
break_exists; break_match; intuition; try congruence.
subst.
find_inversion.
find_apply_lem_hyp In_get_output'.
break_exists; congruence.
-
find_apply_lem_hyp in_remove_all_was_in.
Admitted.

Lemma IRO_in_IR_in_log : forall k log tr, In (IRO k) (log_to_IR (get_output tr) log) -> exists e out, eClient e = fst k /\ eId e = snd k /\ get_output tr k = Some out /\ In e log.
Proof using.
induction log; intros; simpl in *; intuition.
repeat break_match; subst; simpl in *; intuition; try congruence; try find_inversion; simpl.
-
eexists.
eexists.
intuition; eauto.
-
find_apply_hyp_hyp.
break_exists_exists.
intuition.
-
find_apply_hyp_hyp.
break_exists_exists.
Admitted.

Lemma get_output'_In : forall l k out, get_output' l k = Some out -> In (ClientResponse (fst k) (snd k) out) l.
Proof using.
induction l; intros; simpl in *; intuition.
-
discriminate.
-
repeat break_match; subst; eauto.
find_inversion.
break_and.
subst.
Admitted.

Lemma get_output_import_O : forall tr k out, get_output tr k = Some out -> In (O k) (import tr).
Proof using.
induction tr; intros; simpl in *.
-
discriminate.
-
repeat break_match; subst; simpl; intuition eauto.
+
right.
apply remove_preserve; try discriminate.
eauto.
+
find_inversion.
apply in_or_app.
left.
find_apply_lem_hyp get_output'_In.
apply dedup_In.
eapply filterMap_In; eauto.
simpl.
now rewrite <- surjective_pairing.
+
apply in_or_app.
right.
apply in_remove_all_preserve.
*
intro.
find_apply_lem_hyp in_dedup_was_in.
find_apply_lem_hyp In_filterMap.
break_exists.
break_and.
break_match; try discriminate.
find_inversion.
find_apply_lem_hyp In_get_output'.
break_exists.
congruence.
*
Admitted.

Lemma IRU_in_IR_in_log : forall k log tr, In (IRU k) (log_to_IR (get_output tr) log) -> exists e, eClient e = fst k /\ eId e = snd k /\ get_output tr k = None /\ In e log.
Proof using.
induction log; intros; simpl in *; intuition.
repeat break_match; subst; simpl in *; intuition; try congruence; try find_inversion; simpl.
-
find_apply_hyp_hyp.
break_exists_exists.
intuition.
-
eexists.
intuition; eauto.
-
find_apply_hyp_hyp.
break_exists_exists.
Admitted.

Lemma trace_I_in_import : forall tr k h i, In (h, inl (ClientRequest (fst k) (snd k) i)) tr -> In (I k) (import tr).
Proof using.
induction tr; intros; simpl in *; intuition; subst.
-
rewrite <- surjective_pairing.
intuition.
-
break_match; simpl; eauto.
subst.
destruct (key_eq_dec (c, n) k).
+
subst.
auto.
+
right.
apply remove_preserve.
*
congruence.
*
eauto.
-
apply in_or_app.
right.
apply in_remove_all_preserve.
+
intro.
find_apply_lem_hyp in_dedup_was_in.
find_apply_lem_hyp In_filterMap.
break_exists.
break_and.
break_match; try discriminate.
+
Admitted.

Lemma get_IR_input_of_log_to_IR : forall env log, get_IR_input_keys _ (log_to_IR env log) = map (fun e => (eClient e, eId e)) log.
Proof using.
induction log; simpl; intuition.
Admitted.

Lemma get_IR_output_of_log_to_IR : forall env log, get_IR_output_keys _ (log_to_IR env log) = map (fun e => (eClient e, eId e)) log.
Proof using.
induction log; simpl; intuition.
Admitted.

Lemma NoDup_input_import : forall tr, NoDup (get_op_input_keys key (import tr)).
Proof using.
induction tr; intros.
-
constructor.
-
simpl.
repeat break_match; subst.
+
auto.
+
rewrite get_op_input_keys_defn.
constructor; auto.
*
intro.
find_apply_lem_hyp get_op_input_keys_sound.
eapply remove_In; eauto.
*
eapply subseq_NoDup; eauto.
eapply subseq_get_op_input_keys.
auto using subseq_remove.
+
rewrite get_op_input_keys_app.
rewrite get_op_input_keys_on_Os_nil.
*
simpl.
eapply subseq_NoDup; eauto.
eapply subseq_get_op_input_keys.
apply subseq_remove_all.
apply subseq_refl.
*
intros.
find_apply_lem_hyp in_dedup_was_in.
find_apply_lem_hyp In_filterMap.
break_exists.
break_and.
break_match; try discriminate.
subst.
find_inversion.
Admitted.

Lemma NoDup_output_import : forall tr, NoDup (get_op_output_keys key (import tr)).
Proof using.
induction tr; intros.
-
constructor.
-
simpl.
repeat break_match; subst.
+
auto.
+
rewrite get_op_output_keys_defn.
eapply subseq_NoDup; eauto.
apply subseq_get_op_output_keys.
apply subseq_remove.
+
rewrite get_op_output_keys_app.
apply NoDup_disjoint_append.
*
apply get_op_output_keys_preserves_NoDup.
apply NoDup_dedup.
*
eapply subseq_NoDup; eauto.
eapply subseq_get_op_output_keys.
apply subseq_remove_all.
apply subseq_refl.
*
intros.
intro.
repeat find_apply_lem_hyp get_op_output_keys_sound.
Admitted.

Theorem In_get_output' : forall l client id o, In (ClientResponse client id o) l -> exists o', get_output' l (client, id) = Some o'.
Proof using.
intros.
induction l; simpl in *; intuition.
-
subst.
break_if; simpl in *; intuition eauto.
-
break_match; simpl in *; intuition eauto.
break_if; simpl in *; intuition eauto.
