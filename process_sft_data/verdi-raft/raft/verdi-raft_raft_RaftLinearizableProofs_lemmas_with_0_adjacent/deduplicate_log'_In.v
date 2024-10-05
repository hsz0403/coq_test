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
intuition.
