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

Lemma ordered_dynamic_nodes_no_dup : forall onet failed tr, step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, onet) tr -> NoDup (odnwNodes onet).
Proof using.
move => net failed tr H.
remember step_ordered_dynamic_failure_init as y in *.
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init.
rewrite H_init /=.
exact: NoDup_nil.
concludes => {H_init}.
match goal with | [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H end; rewrite //=.
exact: NoDup_cons.
