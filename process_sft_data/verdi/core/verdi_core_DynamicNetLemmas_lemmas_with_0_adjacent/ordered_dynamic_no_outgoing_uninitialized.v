Require Import Verdi.Verdi.
Require Import StructTact.Update.
Require Import FunctionalExtensionality.
Require Import Sumbool.
Require Import Relation_Definitions.
Require Import RelationClasses.
Require Import Verdi.Ssrexport.
Set Implicit Arguments.
Section DynamicNetLemmas.
Context {base_params : BaseParams}.
Context {multi_params : MultiParams base_params}.
Context {overlay_params : NameOverlayParams multi_params}.
Context {new_msg_params : NewMsgParams multi_params}.
Context {fail_msg_params : FailMsgParams multi_params}.
End DynamicNetLemmas.

Lemma ordered_dynamic_no_outgoing_uninitialized : forall onet failed tr, step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> forall n, ~ In n (odnwNodes onet) -> forall n', onet.(odnwPackets) n n' = [].
Proof using.
move => net failed tr H.
remember step_ordered_dynamic_failure_init as y in *.
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
concludes => {H_init}.
match goal with | [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H end; rewrite /=.
-
move => n H_a n'.
have H_neq: h <> n by eauto.
have H_not_in: ~ In n (odnwNodes net0) by eauto.
rewrite collate_ls_not_in; first by rewrite collate_neq //; eauto.
apply: not_in_not_in_filter_rel.
move => H_in.
case: H_not_in.
move: H_in.
exact: in_remove_all_was_in.
-
move => n H_a n'.
have H_neq: to <> n by move => H_eq; rewrite -H_eq in H_a.
rewrite collate_neq //.
rewrite /update2.
case sumbool_and => H_and; last by eauto.
break_and; repeat find_rewrite.
simpl in *.
have IH := IHrefl_trans_1n_trace1 _ H_a.
by find_higher_order_rewrite.
-
move => n H_a n'.
have H_neq: h <> n by move => H_eq; rewrite -H_eq in H_a.
rewrite collate_neq //.
by eauto.
-
move => n H_a n'.
have H_neq: h <> n by move => H_eq; rewrite -H_eq in H_a.
rewrite collate_neq //.
by eauto.
