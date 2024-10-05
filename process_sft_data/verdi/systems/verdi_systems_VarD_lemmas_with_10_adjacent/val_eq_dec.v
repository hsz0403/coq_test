Require Import Verdi.Verdi.
Require Import FMapList.
Require Import String.
Require Import Verdi.FMapVeryWeak.
Require Import Verdi.StateMachineHandlerMonad.
Definition key := string.
Definition value := string.
Inductive input : Set := | Put : key -> value -> input | Get : key -> input | Del : key -> input | CAS : key -> option value -> value -> input | CAD : key -> value -> input.
Inductive output : Set := | Response : key -> option value -> option value -> output.
Module VarDFunctor (Map : VWS with Definition E.t := string with Definition E.eq := @eq string).
Definition key_eq_dec := string_dec.
Definition value_eq_dec := string_dec.
Definition val_eq_dec : forall v v' : option value, {v = v'} + {v <> v'}.
decide equality.
auto using value_eq_dec.
Defined.
Definition trace_state_correct (trace : list (input * output)) (st : data) (st' : data) := forall k, fst (interpret k (rev (inputs_with_key trace k)) (Map.find k st)) = Map.find k st'.
Ltac vard_unfold := unfold runHandler, getk, setk, delk, resp in *; monad_unfold.
Open Scope string_scope.
Example trace_correct_eg0 : trace_correct [(Put "james" "awesome", Response "james" (Some "awesome") None)].
Proof.
rewrite <- app_nil_l.
constructor.
-
constructor.
-
simpl.
auto.
End VarDFunctor.
Module LogTimeVarD := VarDFunctor(LogTimeStringMap).
Module LinearTimeVarD := VarDFunctor(LinearTimeStringMap).
Module VarD := LogTimeVarD.
Export VarD.

Theorem input_eq_dec : forall x y: input, {x = y} + {x <> y}.
Proof.
Admitted.

Theorem output_eq_dec : forall x y: output, {x = y} + {x <> y}.
Proof.
Admitted.

Lemma trace_correct'_trace_correct : forall trace, trace_correct' init trace -> trace_correct trace.
Proof.
intros.
remember init as x.
induction H.
-
constructor.
-
subst.
constructor; auto.
find_rewrite_lem Map.empty_o.
Admitted.

Lemma trace_well_formed : forall st st' trace, step_1_star st st' trace -> (trace = [] \/ exists t i o, trace = t ++ [(i, o)]).
Proof.
intros.
find_apply_lem_hyp refl_trans_1n_n1_trace.
invcs H; intuition.
right.
exists cs.
invcs H1.
unfold VarDHandler, VarDHandler' in *.
vard_unfold.
Admitted.

Lemma inputs_with_key_plus_key : forall l k i o, input_key i = k -> inputs_with_key (l ++ [(i, o)]) k = (inputs_with_key l k) ++ [i].
Proof.
induction l; intros; simpl in *.
-
unfold inputs_with_key.
simpl in *.
repeat break_match; congruence.
-
unfold inputs_with_key in *.
simpl in *.
Admitted.

Lemma inputs_with_key_plus_not_key : forall l k i o, input_key i <> k -> inputs_with_key (l ++ [(i, o)]) k = (inputs_with_key l k).
Proof.
induction l; intros; simpl in *.
-
unfold inputs_with_key.
simpl in *.
repeat break_match; congruence.
-
unfold inputs_with_key in *.
simpl in *.
repeat break_match; simpl in *; eauto; try discriminate.
repeat find_inversion.
f_equal.
Admitted.

Theorem step_1_star_trace_state_correct : forall st st' trace, step_1_star st st' trace -> trace_state_correct trace st st'.
Proof.
intros.
find_apply_lem_hyp refl_trans_1n_n1_trace.
induction H; auto.
-
unfold trace_state_correct.
auto.
-
unfold trace_state_correct in *.
intros.
invcs H0.
unfold VarDHandler, VarDHandler' in *.
vard_unfold.
repeat break_match; simpl in *; repeat find_inversion.
+
destruct (key_eq_dec k0 k).
*
rewrite inputs_with_key_plus_key; simpl in *; auto.
rewrite rev_unit.
simpl in *.
subst.
symmetry; apply Map.add_eq_o.
reflexivity.
*
rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
rewrite Map.add_neq_o; auto.
+
destruct (key_eq_dec k0 k).
*
rewrite inputs_with_key_plus_key; simpl in *; auto.
rewrite rev_unit.
simpl in *.
subst.
eauto.
*
rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
+
destruct (key_eq_dec k0 k).
*
rewrite inputs_with_key_plus_key; simpl in *; auto.
rewrite rev_unit.
simpl in *.
subst.
eauto.
rewrite Map.remove_eq_o; auto.
*
rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
rewrite Map.remove_neq_o; auto.
+
destruct (key_eq_dec k0 k).
*
subst.
rewrite inputs_with_key_plus_key; simpl in *; auto.
rewrite rev_unit.
simpl in *.
break_if; [rewrite Map.add_eq_o; auto | idtac].
exfalso.
intuition.
*
rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
rewrite Map.add_neq_o; auto.
+
destruct (key_eq_dec k0 k).
*
rewrite inputs_with_key_plus_key; simpl in *; auto.
rewrite rev_unit.
simpl in *.
subst.
break_if.
--
subst.
exfalso.
intuition.
--
simpl in *.
apply IHrefl_trans_n1_trace.
*
rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
+
destruct (key_eq_dec k0 k).
*
{
subst.
rewrite inputs_with_key_plus_key; simpl in *; auto.
rewrite rev_unit.
simpl in *.
break_if; simpl in *.
-
symmetry.
rewrite Map.remove_eq_o; auto.
-
exfalso.
intuition.
match goal with | H : _ -> False |- _ => apply H end.
find_higher_order_rewrite.
auto.
}
*
rewrite inputs_with_key_plus_not_key; simpl in *; eauto.
rewrite Map.remove_neq_o; auto.
+
destruct (key_eq_dec k0 k).
*
subst.
rewrite inputs_with_key_plus_key; simpl in *; auto.
rewrite rev_unit.
simpl in *.
break_if; simpl in *; intuition.
exfalso.
intuition.
match goal with | H : _ -> False |- _ => apply H end.
find_higher_order_rewrite.
auto.
*
Admitted.

Lemma trace_state_correct_trace_correct : forall st st' st'' trace t, trace_state_correct trace st st' -> trace_correct' st trace -> step_1 st' st'' t -> trace_correct' st (trace ++ t).
Proof.
intros.
invcs H1; simpl in *.
unfold VarDHandler, VarDHandler' in *.
vard_unfold.
Admitted.

Theorem step_1_star_trace_correct' : forall st st' trace, step_1_star st st' trace -> trace_correct' st trace.
Proof.
intros.
find_apply_lem_hyp refl_trans_1n_n1_trace.
induction H.
-
constructor.
-
find_apply_lem_hyp refl_trans_n1_1n_trace.
find_apply_lem_hyp step_1_star_trace_state_correct; auto.
Admitted.

Theorem step_1_star_trace_correct : forall st trace, step_1_star init st trace -> trace_correct trace.
Proof.
intros.
find_apply_lem_hyp step_1_star_trace_correct'.
Admitted.

Definition val_eq_dec : forall v v' : option value, {v = v'} + {v <> v'}.
decide equality.
auto using value_eq_dec.
