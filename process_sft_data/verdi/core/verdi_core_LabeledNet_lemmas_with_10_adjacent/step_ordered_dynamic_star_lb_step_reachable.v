Require Import Verdi.Verdi.
Require Import InfSeqExt.infseq.
Require Import InfSeqExt.exteq.
Require Import Verdi.Ssrexport.
Set Implicit Arguments.
Class LabeledMultiParams (P : BaseParams) := { lb_name : Type ; lb_msg : Type ; lb_msg_eq_dec : forall x y : lb_msg, {x = y} + {x <> y} ; lb_name_eq_dec : forall x y : lb_name, {x = y} + {x <> y} ; lb_nodes : list lb_name ; lb_all_names_nodes : forall n, In n lb_nodes ; lb_no_dup_nodes : NoDup lb_nodes ; label : Type ; label_silent : label ; lb_init_handlers : lb_name -> data ; lb_net_handlers : lb_name -> lb_name -> lb_msg -> data -> label * (list output) * data * list (lb_name * lb_msg) ; lb_input_handlers : lb_name -> input -> data -> label * (list output) * data * list (lb_name * lb_msg) }.
Section UnlabeledParams.
Context {base_params : BaseParams}.
Context {labeled_multi_params : LabeledMultiParams base_params}.
Definition unlabeled_net_handlers me src m st := let '(lb, out, st', ps) := lb_net_handlers me src m st in (out, st', ps).
Definition unlabeled_input_handlers me inp st := let '(lb, out, st', ps) := lb_input_handlers me inp st in (out, st', ps).
Global Instance unlabeled_multi_params : MultiParams base_params := { name := lb_name ; msg := lb_msg ; msg_eq_dec := lb_msg_eq_dec ; name_eq_dec := lb_name_eq_dec ; nodes := lb_nodes ; all_names_nodes := lb_all_names_nodes ; no_dup_nodes := lb_no_dup_nodes ; init_handlers := lb_init_handlers; net_handlers := unlabeled_net_handlers ; input_handlers := unlabeled_input_handlers }.
End UnlabeledParams.
Section LabeledStepExecution.
Variable A : Type.
Variable L : Type.
Variable trace : Type.
Definition lb_step_relation := A -> L -> A -> list trace -> Prop.
Definition lb_step_ex (step : lb_step_relation) (l : L) (a : A) : Prop := exists a' tr, step a l a' tr.
Record event := { evt_a : A ; evt_l : L ; evt_trace : list trace }.
Definition enabled (step : lb_step_relation) (l : L) (e : event) : Prop := lb_step_ex step l (evt_a e).
Definition occurred (l : L) (e : event) : Prop := l = evt_l e.
Definition inf_enabled (step : lb_step_relation) (l : L) (s : infseq event) : Prop := inf_often (now (enabled step l)) s.
Definition cont_enabled (step : lb_step_relation) (l : L) (s : infseq event) : Prop := continuously (now (enabled step l)) s.
Definition inf_occurred (l : L) (s : infseq event) : Prop := inf_often (now (occurred l)) s.
Definition strong_fairness (step : lb_step_relation) (silent : L) (s : infseq event) : Prop := forall l : L, l <> silent -> inf_enabled step l s -> inf_occurred l s.
Definition weak_fairness (step : lb_step_relation) (silent : L) (s : infseq event) : Prop := forall l : L, l <> silent -> cont_enabled step l s -> inf_occurred l s.
CoInductive lb_step_execution (step : lb_step_relation) : infseq event -> Prop := Cons_lb_step_exec : forall (e e' : event) (tr : list trace) (s : infseq event), step (evt_a e) (evt_l e) (evt_a e') tr -> evt_trace e' = evt_trace e ++ tr -> lb_step_execution step (Cons e' s) -> lb_step_execution step (Cons e (Cons e' s)).
Definition event_step_star (step : step_relation A trace) (init : A) (e : event) := refl_trans_1n_trace step init (evt_a e) (evt_trace e).
Definition step_star_lb_step_reachable (lb_step : lb_step_relation) (step : step_relation A trace) (init : A) := forall a l a' tr tr', refl_trans_1n_trace step init a tr' -> lb_step a l a' tr -> refl_trans_1n_trace step init a' (tr' ++ tr).
End LabeledStepExecution.
Section LabeledStepAsync.
Context `{labeled_multi_params : LabeledMultiParams}.
Inductive lb_step_async : lb_step_relation network label (name * (input + list output)) := | LabeledStepAsync_deliver : forall net net' p xs ys out d l lb, nwPackets net = xs ++ p :: ys -> lb_net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (lb, out, d, l) -> net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys) (update name_eq_dec (nwState net) (pDst p) d) -> lb_step_async net lb net' [(pDst p, inr out)] | LabeledStepAsync_input : forall h net net' out inp d l lb, lb_input_handlers h inp (nwState net h) = (lb, out, d, l) -> net' = mkNetwork (send_packets h l ++ nwPackets net) (update name_eq_dec (nwState net) h d) -> lb_step_async net lb net' [(h, inl inp); (h, inr out)] | LabeledStepAsync_stutter : forall net, lb_step_async net label_silent net [].
End LabeledStepAsync.
Section LabeledStepFailure.
Context `{labeled_multi_params : LabeledMultiParams}.
Inductive lb_step_failure : lb_step_relation (list name * network) label (name * (input + list output)) := | LabeledStepFailure_deliver : forall net net' failed p xs ys out d l lb, nwPackets net = xs ++ p :: ys -> ~ In (pDst p) failed -> lb_net_handlers (pDst p) (pSrc p) (pBody p) (nwState net (pDst p)) = (lb, out, d, l) -> net' = mkNetwork (send_packets (pDst p) l ++ xs ++ ys) (update name_eq_dec (nwState net) (pDst p) d) -> lb_step_failure (failed, net) lb (failed, net') [(pDst p, inr out)] | LabeledStepFailure_input : forall h net net' failed out inp d l lb, ~ In h failed -> lb_input_handlers h inp (nwState net h) = (lb, out, d, l) -> net' = mkNetwork (send_packets h l ++ nwPackets net) (update name_eq_dec (nwState net) h d) -> lb_step_failure (failed, net) lb (failed, net') [(h, inl inp); (h, inr out)] | LabeledStepFailure_stutter : forall net failed, lb_step_failure (failed, net) label_silent (failed, net) [].
Context {failure_params : FailureParams unlabeled_multi_params}.
End LabeledStepFailure.
Section LabeledStepOrderFailure.
Context `{labeled_multi_params : LabeledMultiParams}.
Inductive lb_step_ordered_failure : lb_step_relation (list name * ordered_network) label (name * (input + output)) := | LabeledStepOrderedFailure_deliver : forall net net' failed tr m ms out d l from to lb, onwPackets net from to = m :: ms -> ~ In to failed -> lb_net_handlers to from m (onwState net to) = (lb, out, d, l) -> net' = mkONetwork (collate name_eq_dec to (update2 name_eq_dec (onwPackets net) from to ms) l) (update name_eq_dec (onwState net) to d) -> tr = map2fst to (map inr out) -> lb_step_ordered_failure (failed, net) lb (failed, net') tr | LabeledStepOrderedFailure_input : forall h net net' failed tr out inp d l lb, ~ In h failed -> lb_input_handlers h inp (onwState net h) = (lb, out, d, l) -> net' = mkONetwork (collate name_eq_dec h (onwPackets net) l) (update name_eq_dec (onwState net) h d) -> tr = (h, inl inp) :: map2fst h (map inr out) -> lb_step_ordered_failure (failed, net) lb (failed, net') tr | LabeledStepOrderedFailure_stutter : forall net failed, lb_step_ordered_failure (failed, net) label_silent (failed, net) [].
Context {overlay_params : NameOverlayParams unlabeled_multi_params}.
Context {fail_msg_params : FailMsgParams unlabeled_multi_params}.
End LabeledStepOrderFailure.
Section LabeledStepOrderDynamic.
Context `{labeled_multi_params : LabeledMultiParams}.
Inductive lb_step_ordered_dynamic : lb_step_relation ordered_dynamic_network label (name * (input + output)) := | LabeledStepOrderedDynamic_deliver : forall net net' tr m ms out d d' l from to lb, In to (odnwNodes net) -> odnwState net to = Some d -> odnwPackets net from to = m :: ms -> lb_net_handlers to from m d = (lb, out, d', l) -> net' = {| odnwNodes := odnwNodes net; odnwPackets := collate name_eq_dec to (update2 name_eq_dec (odnwPackets net) from to ms) l; odnwState := update name_eq_dec (odnwState net) to (Some d') |} -> tr = map2fst to (map inr out) -> lb_step_ordered_dynamic net lb net' tr | LabeledStepOrderedDynamic_input : forall h net net' tr out inp d d' l lb, In h (odnwNodes net) -> odnwState net h = Some d -> lb_input_handlers h inp d = (lb, out, d', l) -> net' = {| odnwNodes := odnwNodes net; odnwPackets := collate name_eq_dec h (odnwPackets net) l; odnwState := update name_eq_dec (odnwState net) h (Some d') |} -> tr = (h, inl inp) :: map2fst h (map inr out) -> lb_step_ordered_dynamic net lb net' tr | LabeledStepOrderedDynamic_stutter : forall net, lb_step_ordered_dynamic net label_silent net [].
Context {overlay_params : NameOverlayParams unlabeled_multi_params}.
Context {new_msg_params : NewMsgParams unlabeled_multi_params}.
End LabeledStepOrderDynamic.
Section LabeledStepOrderDynamicFailure.
Context `{labeled_multi_params : LabeledMultiParams}.
Inductive lb_step_ordered_dynamic_failure : lb_step_relation (list name * ordered_dynamic_network) label (name * (input + output)) := | LabeledStepOrderedDynamicFailure_deliver : forall net net' failed tr m ms out d d' l from to lb, ~ In to failed -> In to (odnwNodes net) -> odnwState net to = Some d -> odnwPackets net from to = m :: ms -> lb_net_handlers to from m d = (lb, out, d', l) -> net' = {| odnwNodes := odnwNodes net; odnwPackets := collate name_eq_dec to (update2 name_eq_dec (odnwPackets net) from to ms) l; odnwState := update name_eq_dec (odnwState net) to (Some d') |} -> tr = map2fst to (map inr out) -> lb_step_ordered_dynamic_failure (failed, net) lb (failed, net') tr | LabeledStepOrderedDynamicFailure_input : forall h net net' failed tr out inp d d' l lb, ~ In h failed -> In h (odnwNodes net) -> odnwState net h = Some d -> lb_input_handlers h inp d = (lb, out, d', l) -> net' = {| odnwNodes := odnwNodes net; odnwPackets := collate name_eq_dec h (odnwPackets net) l; odnwState := update name_eq_dec (odnwState net) h (Some d') |} -> tr = (h, inl inp) :: map2fst h (map inr out) -> lb_step_ordered_dynamic_failure (failed, net) lb (failed, net') tr | LabeledStepOrderedDynamicFailure_stutter : forall net failed, lb_step_ordered_dynamic_failure (failed, net) label_silent (failed, net) [].
Context {overlay_params : NameOverlayParams unlabeled_multi_params}.
Context {fail_msg_params : FailMsgParams unlabeled_multi_params}.
Context {new_msg_params : NewMsgParams unlabeled_multi_params}.
End LabeledStepOrderDynamicFailure.
Hint Extern 4 (@LabeledMultiParams _) => apply unlabeled_multi_params : typeclass_instances.

Lemma strong_fairness_weak : forall step silent s, strong_fairness step silent s -> weak_fairness step silent s.
Proof using.
move => step silent.
case => e s.
rewrite /strong_fairness /weak_fairness /inf_enabled /cont_enabled.
move => H_str l neq H_cont.
apply: H_str; first by [].
Admitted.

Lemma lb_step_execution_invar : forall step x s, lb_step_execution step (Cons x s) -> lb_step_execution step s.
Proof using.
intros step x s e.
change (lb_step_execution step (tl (Cons x s))).
destruct e; simpl.
Admitted.

Lemma lb_step_execution_extensional : forall step, extensional (lb_step_execution step).
Proof using.
move => step.
rewrite /extensional /=.
cofix c.
case => e1; case => e1' s1.
case => e2; case => e2' s2 H_eq.
find_apply_lem_hyp exteq_inversion.
break_and.
find_copy_apply_lem_hyp exteq_inversion.
break_and.
repeat find_rewrite.
move => H_exec.
inversion H_exec; subst.
apply (Cons_lb_step_exec _ tr) => //.
Admitted.

Lemma step_star_lb_step_execution : forall lb_step step init, step_star_lb_step_reachable lb_step step init -> forall s, event_step_star step init (hd s) -> lb_step_execution lb_step s -> always (now (event_step_star step init)) s.
Proof using.
move => lb_step step init H_r.
case => e s H_star.
move: e s H_star.
cofix cf.
move => e.
case => e' s H_star H_exec'.
constructor; first by [].
apply cf.
inversion H_exec'; subst_max.
simpl in *.
rewrite /event_step_star /=.
rewrite /event_step_star /= in H_star.
rewrite /step_star_lb_step_reachable in H_r.
have H_d := H_r _ _ _ _ _ H_star H2.
rewrite H3.
exact: H_r _ _ _ _ _ H_star H2.
move: H_exec'.
Admitted.

Lemma step_async_star_lb_step_reachable : step_star_lb_step_reachable lb_step_async step_async step_async_init.
Proof using.
rewrite /step_star_lb_step_reachable.
move => net l.
move => net' tr tr' H_star H_st.
invcs H_st.
-
set net' := {| nwPackets := _ ; nwState := _ |}.
apply (@refl_trans_1n_trace_trans _ _ _ _ net) => //.
have ->: [(pDst p, inr out)] = [(pDst p, inr out)] ++ [] by [].
apply: (@RT1nTStep _ _ _ _ net'); last exact: RT1nTBase.
apply: (@StepAsync_deliver _ _ _ _ _ xs ys _ d l0) => //.
rewrite /net_handlers /= /unlabeled_net_handlers /=.
repeat break_let.
by tuple_inversion.
-
set net' := {| nwPackets := _ ; nwState := _ |}.
apply (@refl_trans_1n_trace_trans _ _ _ _ net) => //.
have ->: [(h, inl inp); (h, inr out)] = [(h, inl inp); (h, inr out)] ++ [] by [].
apply: (@RT1nTStep _ _ _ _ net'); last exact: RT1nTBase.
apply: StepAsync_input => //.
rewrite /input_handlers /= /unlabeled_input_handlers /=.
repeat break_let.
by tuple_inversion.
-
Admitted.

Lemma step_async_star_lb_step_execution : forall s, event_step_star step_async step_async_init (hd s) -> lb_step_execution lb_step_async s -> always (now (event_step_star step_async step_async_init)) s.
Proof using.
apply: step_star_lb_step_execution.
Admitted.

Lemma step_failure_star_lb_step_reachable : step_star_lb_step_reachable lb_step_failure step_failure step_failure_init.
Proof using.
rewrite /step_star_lb_step_reachable.
case => failed net l.
case => failed' net' tr tr' H_star H_st.
invcs H_st.
-
set net' := {| nwPackets := _ ; nwState := _ |}.
apply (@refl_trans_1n_trace_trans _ _ _ _ (failed', net)) => //.
have ->: [(pDst p, inr out)] = [(pDst p, inr out)] ++ [] by [].
apply: (@RT1nTStep _ _ _ _ (failed', net')); last exact: RT1nTBase.
apply: (@StepFailure_deliver _ _ _ _ _ _ _ xs ys _ d l0) => //.
rewrite /net_handlers /= /unlabeled_net_handlers /=.
repeat break_let.
by tuple_inversion.
-
set net' := {| nwPackets := _ ; nwState := _ |}.
apply (@refl_trans_1n_trace_trans _ _ _ _ (failed', net)) => //.
have ->: [(h, inl inp); (h, inr out)] = [(h, inl inp); (h, inr out)] ++ [] by [].
apply: (@RT1nTStep _ _ _ _ (failed', net')); last exact: RT1nTBase.
apply: StepFailure_input => //.
rewrite /input_handlers /= /unlabeled_input_handlers /=.
repeat break_let.
by tuple_inversion.
-
Admitted.

Lemma step_failure_star_lb_step_execution : forall s, event_step_star step_failure step_failure_init (hd s) -> lb_step_execution lb_step_failure s -> always (now (event_step_star step_failure step_failure_init)) s.
Proof using.
apply: step_star_lb_step_execution.
Admitted.

Lemma step_ordered_failure_star_lb_step_reachable : step_star_lb_step_reachable lb_step_ordered_failure step_ordered_failure step_ordered_failure_init.
Proof using.
rewrite /step_star_lb_step_reachable.
case => failed net l.
case => failed' net' tr tr' H_star H_st.
invcs H_st.
-
set net' := {| onwPackets := _ ; onwState := _ |}.
apply (@refl_trans_1n_trace_trans _ _ _ _ (failed', net)) => //.
rewrite (app_nil_end (map2fst _ _)).
apply: (@RT1nTStep _ _ _ _ (failed', net')); last exact: RT1nTBase.
apply: (StepOrderedFailure_deliver _ _ _ H3) => //.
rewrite /net_handlers /= /unlabeled_net_handlers /=.
repeat break_let.
by tuple_inversion.
-
set net' := {| onwPackets := _ ; onwState := _ |}.
apply (@refl_trans_1n_trace_trans _ _ _ _ (failed', net)) => //.
rewrite (app_nil_end (_ :: _)).
apply: (@RT1nTStep _ _ _ _ (failed', net')); last exact: RT1nTBase.
apply: StepOrderedFailure_input => //; first by [].
rewrite /input_handlers /= /unlabeled_input_handlers /=.
repeat break_let.
by tuple_inversion.
-
Admitted.

Lemma step_ordered_failure_star_lb_step_execution : forall s, event_step_star step_ordered_failure step_ordered_failure_init (hd s) -> lb_step_execution lb_step_ordered_failure s -> always (now (event_step_star step_ordered_failure step_ordered_failure_init)) s.
Proof using.
apply: step_star_lb_step_execution.
Admitted.

Lemma step_ordered_dynamic_star_lb_step_execution : forall s, event_step_star step_ordered_dynamic step_ordered_dynamic_init (hd s) -> lb_step_execution lb_step_ordered_dynamic s -> always (now (event_step_star step_ordered_dynamic step_ordered_dynamic_init)) s.
Proof using.
apply: step_star_lb_step_execution.
Admitted.

Lemma step_ordered_dynamic_failure_star_lb_step_reachable : step_star_lb_step_reachable lb_step_ordered_dynamic_failure step_ordered_dynamic_failure step_ordered_dynamic_failure_init.
Proof using.
rewrite /step_star_lb_step_reachable.
case => failed net l.
case => failed' net' tr tr' H_star H_st.
invcs H_st.
-
set net' := {| odnwNodes := _ ; odnwPackets := _ ; odnwState := _ |}.
apply (@refl_trans_1n_trace_trans _ _ _ _ (failed', net)) => //.
rewrite (app_nil_end (map2fst _ _)).
apply: (@RT1nTStep _ _ _ _ (failed', net')); last exact: RT1nTBase.
apply: (StepOrderedDynamicFailure_deliver _ _ _ _ _ H5 H6) => //.
rewrite /net_handlers /= /unlabeled_net_handlers /=.
repeat break_let.
by tuple_inversion.
-
set net' := {| odnwNodes := _ ; odnwPackets := _ ; odnwState := _ |}.
apply (@refl_trans_1n_trace_trans _ _ _ _ (failed', net)) => //.
rewrite (app_nil_end (_ :: _)).
apply: (@RT1nTStep _ _ _ _ (failed', net')); last exact: RT1nTBase.
apply: (StepOrderedDynamicFailure_input _ _ _ _ H5) => //.
rewrite /input_handlers /= /unlabeled_input_handlers /=.
repeat break_let.
by tuple_inversion.
-
Admitted.

Lemma step_ordered_dynamic_failure_star_lb_step_execution : forall s, event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init (hd s) -> lb_step_execution lb_step_ordered_dynamic_failure s -> always (now (event_step_star step_ordered_dynamic_failure step_ordered_dynamic_failure_init)) s.
Proof using.
apply: step_star_lb_step_execution.
Admitted.

Lemma step_ordered_dynamic_star_lb_step_reachable : step_star_lb_step_reachable lb_step_ordered_dynamic step_ordered_dynamic step_ordered_dynamic_init.
Proof using.
rewrite /step_star_lb_step_reachable.
move => net l.
move => net' tr tr' H_star H_st.
invcs H_st.
-
set net' := {| odnwNodes := _ ; odnwPackets := _ ; odnwState := _ |}.
apply (@refl_trans_1n_trace_trans _ _ _ _ net) => //.
rewrite (app_nil_end (map2fst _ _)).
apply: (@RT1nTStep _ _ _ _ net'); last exact: RT1nTBase.
apply: (StepOrderedDynamic_deliver _ _ _ H0 H1) => //.
rewrite /net_handlers /= /unlabeled_net_handlers /=.
repeat break_let.
by tuple_inversion.
-
set net' := {| odnwNodes := _ ; odnwPackets := _ ; odnwState := _ |}.
apply (@refl_trans_1n_trace_trans _ _ _ _ net) => //.
rewrite (app_nil_end (_ :: _)).
apply: (@RT1nTStep _ _ _ _ net'); last exact: RT1nTBase.
apply: (StepOrderedDynamic_input _ _ H0) => //.
rewrite /input_handlers /= /unlabeled_input_handlers /=.
repeat break_let.
by tuple_inversion.
-
by have ->: tr' ++ [] = tr' by auto with datatypes.
