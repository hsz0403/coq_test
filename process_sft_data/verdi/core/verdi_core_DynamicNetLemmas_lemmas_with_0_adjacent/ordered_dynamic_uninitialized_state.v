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

Lemma ordered_dynamic_uninitialized_state : forall net failed tr, step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> forall n, ~ In n (odnwNodes net) -> odnwState net n = None.
Proof using.
move => net failed tr H.
remember step_ordered_dynamic_failure_init as y in *.
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
concludes => {H_init}.
match goal with | [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H end; rewrite /=.
-
move => n H_in.
rewrite /= in IHrefl_trans_1n_trace1.
rewrite /update /=.
have H_neq: h <> n by move => H_eq; case: H_in; left.
have H_not_in: ~ In n (odnwNodes net0) by move => H_not_in; case: H_in; right.
case name_eq_dec => H_dec; first by rewrite H_dec in H_neq.
exact: IHrefl_trans_1n_trace1.
-
move => n H_in.
rewrite /= in IHrefl_trans_1n_trace1.
rewrite /update /=.
have H_neq: n <> to by move => H_eq; rewrite H_eq in H_in.
case name_eq_dec => H_dec //.
exact: IHrefl_trans_1n_trace1.
-
move => n H_in.
rewrite /= in IHrefl_trans_1n_trace1.
rewrite /update.
have H_neq: n <> h by move => H_eq; rewrite H_eq in H_in.
case name_eq_dec => H_dec //.
exact: IHrefl_trans_1n_trace1.
-
move => n H_in.
rewrite /= in IHrefl_trans_1n_trace1.
exact: IHrefl_trans_1n_trace1.
