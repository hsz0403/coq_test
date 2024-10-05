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

Lemma ordered_dynamic_failed_then_initialized : forall net failed tr, step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> forall n, In n failed -> In n (odnwNodes net).
Proof using.
move => net failed tr H.
remember step_ordered_dynamic_failure_init as y in *.
have ->: failed = fst (failed, net) by [].
have H_eq_o: net = snd (failed, net) by [].
rewrite {2}H_eq_o {H_eq_o}.
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
repeat find_rewrite.
concludes => {H_init}.
match goal with | [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H end; rewrite /=.
-
move => n H_in.
right.
exact: IHrefl_trans_1n_trace1.
-
move => n H_in.
exact: IHrefl_trans_1n_trace1.
-
move => n H_in.
exact: IHrefl_trans_1n_trace1.
-
move => n H_in.
case: H_in => H_in; first by rewrite -H_in.
exact: IHrefl_trans_1n_trace1.
