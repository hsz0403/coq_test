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

Lemma ordered_dynamic_initialized_state : forall net failed tr, step_ordered_dynamic_failure_star step_ordered_dynamic_failure_init (failed, net) tr -> forall n, In n (odnwNodes net) -> exists d, odnwState net n = Some d.
Proof using.
move => net failed tr H.
remember step_ordered_dynamic_failure_init as y in *.
have ->: net = snd (failed, net) by [].
move: Heqy.
induction H using refl_trans_1n_trace_n1_ind => H_init /=; first by rewrite H_init.
repeat find_rewrite.
concludes => {H_init}.
match goal with | [ H : step_ordered_dynamic_failure _ _ _ |- _ ] => invc H end; rewrite /=.
-
move => n H_in.
case: H_in => H_in.
rewrite -H_in /update.
break_if => //.
by exists (init_handlers h).
have H_neq: n <> h by move => H_eq; rewrite H_eq in H_in.
have [d H_eq] := IHrefl_trans_1n_trace1 _ H_in.
exists d.
rewrite /update /=.
by break_if.
-
move => n H_in.
rewrite /update.
break_if; first by exists d'.
have [d0 H_eq] := IHrefl_trans_1n_trace1 _ H_in.
by exists d0.
-
move => n H_in.
rewrite /update.
break_if; first by exists d'.
have [d0 H_eq] := IHrefl_trans_1n_trace1 _ H_in.
by exists d0.
-
move => n H_in.
exact: IHrefl_trans_1n_trace1.
