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
}
