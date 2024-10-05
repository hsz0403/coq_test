Require Import Verdi.Verdi.
Require Import Verdi.LabeledNet.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.
Require Import Verdi.TotalMapExecutionSimulations.
Require Import InfSeqExt.infseq.
Require Import InfSeqExt.map.
Require Import InfSeqExt.exteq.
Require Import FunctionalExtensionality.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import Verdi.Ssrexport.
Require Import ssr.ssrbool.
Set Implicit Arguments.
Class LabeledMultiParamsPartialMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : LabeledMultiParams B0) (P1 : LabeledMultiParams B1) (B : BaseParamsPartialMap B0 B1) (N : MultiParamsNameTotalMap (@unlabeled_multi_params _ P0) (@unlabeled_multi_params _ P1)) (P : MultiParamsMsgPartialMap (@unlabeled_multi_params _ P0) (@unlabeled_multi_params _ P1)) (L : LabeledMultiParamsLabelTotalMap P0 P1) : Prop := { pt_lb_label_silent_fst_snd : tot_map_label label_silent = label_silent ; pt_lb_net_handlers_some : forall me src m st m' out st' ps lb, pt_map_msg m = Some m' -> lb_net_handlers (tot_map_name me) (tot_map_name src) m' (pt_map_data st) = (lb, out, st', ps) -> lb <> label_silent /\ tot_mapped_lb_net_handlers_label me src m st = lb ; pt_lb_net_handlers_none : forall me src m st, pt_map_msg m = None -> tot_mapped_lb_net_handlers_label me src m st = label_silent ; pt_lb_input_handlers_some : forall me inp st inp' out st' ps lb, pt_map_input inp = Some inp' -> lb_input_handlers (tot_map_name me) inp' (pt_map_data st) = (lb, out, st', ps) -> lb <> label_silent /\ tot_mapped_lb_input_handlers_label me inp st = lb ; pt_lb_input_handlers_none : forall me inp st, pt_map_input inp = None -> tot_mapped_lb_input_handlers_label me inp st = label_silent }.
Section PartialMapExecutionSimulations.
Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {labeled_multi_fst : LabeledMultiParams base_fst}.
Context {labeled_multi_snd : LabeledMultiParams base_snd}.
Context {base_map : BaseParamsPartialMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap (@unlabeled_multi_params _ labeled_multi_fst) (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {msg_map : MultiParamsMsgPartialMap (@unlabeled_multi_params _ labeled_multi_fst) (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {label_map : LabeledMultiParamsLabelTotalMap labeled_multi_fst labeled_multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsPartialMapCongruency base_map name_map msg_map}.
Context {multi_map_lb_congr : LabeledMultiParamsPartialMapCongruency base_map name_map msg_map label_map}.
Hypothesis label_eq_dec : forall x y : label, {x = y} + {x <> y}.
Hypothesis tot_map_label_injective : forall l l', tot_map_label l = tot_map_label l' -> l = l'.
Hypothesis label_tot_mapped : forall l, exists l', l = tot_map_label l'.
Definition pt_map_onet_event e := {| evt_a := (List.map tot_map_name (fst e.(evt_a)), pt_map_onet (snd e.(evt_a))) ; evt_l := tot_map_label e.(evt_l) ; evt_trace := filterMap pt_map_trace_ev e.(evt_trace) |}.
Hypothesis lb_step_ordered_failure_strong_fairness_enabled_pt_map_onet_eventually : forall l, tot_map_label l <> label_silent -> forall s, lb_step_execution lb_step_ordered_failure s -> strong_fairness lb_step_ordered_failure label_silent s -> enabled lb_step_ordered_failure (tot_map_label l) (pt_map_onet_event (hd s)) -> eventually (now (enabled lb_step_ordered_failure l)) s.
Hypothesis lb_step_ordered_failure_weak_fairness_always_enabled_pt_map_onet_continuously : forall l, tot_map_label l <> label_silent -> forall s, lb_step_execution lb_step_ordered_failure s -> weak_fairness lb_step_ordered_failure label_silent s -> always (now (enabled lb_step_ordered_failure (tot_map_label l))) (map pt_map_onet_event s) -> continuously (now (enabled lb_step_ordered_failure l)) s.
Context {overlay_fst : NameOverlayParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {overlay_snd : NameOverlayParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {overlay_map_congr : NameOverlayParamsTotalMapCongruency overlay_fst overlay_snd name_map}.
Context {fail_msg_fst : FailMsgParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {fail_msg_snd : FailMsgParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {fail_msg_map_congr : FailMsgParamsPartialMapCongruency fail_msg_fst fail_msg_snd msg_map}.
Definition pt_map_odnet_event e := {| evt_a := (List.map tot_map_name (fst e.(evt_a)), pt_map_odnet (snd e.(evt_a))) ; evt_l := tot_map_label e.(evt_l) ; evt_trace := filterMap pt_map_trace_ev e.(evt_trace) |}.
Hypothesis lb_step_ordered_dynamic_failure_strong_fairness_enabled_pt_map_onet_eventually : forall l, tot_map_label l <> label_silent -> forall s, lb_step_execution lb_step_ordered_dynamic_failure s -> strong_fairness lb_step_ordered_dynamic_failure label_silent s -> enabled lb_step_ordered_dynamic_failure (tot_map_label l) (pt_map_odnet_event (hd s)) -> eventually (now (enabled lb_step_ordered_dynamic_failure l)) s.
Hypothesis lb_step_ordered_dynamic_failure_weak_fairness_always_enabled_pt_map_onet_continuously : forall l, tot_map_label l <> label_silent -> forall s, lb_step_execution lb_step_ordered_dynamic_failure s -> weak_fairness lb_step_ordered_dynamic_failure label_silent s -> always (now (enabled lb_step_ordered_dynamic_failure (tot_map_label l))) (map pt_map_odnet_event s) -> continuously (now (enabled lb_step_ordered_dynamic_failure l)) s.
Context {new_msg_fst : NewMsgParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {new_msg_snd : NewMsgParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {new_msg_map_congr : NewMsgParamsPartialMapCongruency new_msg_fst new_msg_snd msg_map}.
End PartialMapExecutionSimulations.

Theorem lb_step_failure_pt_mapped_simulation_1_non_silent : forall net net' failed failed' lb tr, tot_map_label lb <> label_silent -> @lb_step_failure _ labeled_multi_fst (failed, net) lb (failed', net') tr -> @lb_step_failure _ labeled_multi_snd (List.map tot_map_name failed, pt_map_net net) (tot_map_label lb) (List.map tot_map_name failed', pt_map_net net') (filterMap pt_map_trace_occ tr).
Proof using name_map_bijective multi_map_lb_congr multi_map_congr.
move => net net' failed failed' lb tr H_neq H_step.
have H_neq': lb <> label_silent.
rewrite -pt_lb_label_silent_fst_snd in H_neq.
move => H_eq.
by rewrite H_eq in H_neq.
invcs H_step => //=.
-
destruct (pt_map_packet p) eqn:?; last first.
destruct p.
simpl in *.
break_match => //.
have H_q := @pt_lb_net_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr pDst pSrc _ (nwState net pDst) Heqo0.
rewrite /tot_mapped_lb_net_handlers_label in H_q.
repeat break_let.
by tuple_inversion.
have H_eq_n: tot_map_name (pDst p) = pDst p0.
destruct p.
simpl in *.
break_match => //.
by find_injection.
rewrite H_eq_n.
apply (@LabeledStepFailure_deliver _ _ _ _ _ _ (filterMap pt_map_packet xs) (filterMap pt_map_packet ys) (filterMap pt_map_output out) (pt_map_data d) (filterMap (@pt_map_name_msg _ _ _ _ _ msg_map) l)).
*
rewrite /pt_map_net /=.
find_rewrite.
by rewrite filterMap_app /= Heqo.
*
rewrite -H_eq_n.
exact: not_in_failed_not_in.
*
rewrite /pt_map_net /= -{2}H_eq_n tot_map_name_inv_inverse.
destruct p, p0.
simpl in *.
break_match => //.
find_injection.
clean.
have H_q := @pt_net_handlers_some _ _ _ _ _ _ _ multi_map_congr pDst pSrc pBody (nwState net pDst) _ Heqo0.
rewrite /pt_mapped_net_handlers /net_handlers /= /unlabeled_net_handlers in H_q.
repeat break_let.
repeat tuple_inversion.
have H_q' := @pt_lb_net_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ _ Heqo0 Heqp1.
rewrite /tot_mapped_lb_net_handlers_label in H_q'.
repeat break_let.
break_and.
by repeat tuple_inversion.
*
rewrite /pt_map_net /= 2!filterMap_app.
by rewrite (filterMap_pt_map_packet_map_eq_some _ _ Heqo) (pt_map_update_eq_some _ _ _ Heqo).
-
case H_i: pt_map_input => [inp'|]; last first.
have H_q := @pt_lb_input_handlers_none _ _ _ _ _ _ _ _ multi_map_lb_congr h _ (nwState net h) H_i.
rewrite /tot_mapped_lb_input_handlers_label /= in H_q.
repeat break_let.
by tuple_inversion.
apply (@LabeledStepFailure_input _ _ _ _ _ _ _ _ (pt_map_data d) (filterMap (@pt_map_name_msg _ _ _ _ _ msg_map) l)).
*
exact: not_in_failed_not_in.
*
have H_q := @pt_input_handlers_some _ _ _ _ _ _ _ multi_map_congr h _ (nwState net h) _ H_i.
rewrite /pt_mapped_input_handlers /input_handlers /= /unlabeled_input_handlers in H_q.
repeat break_let.
repeat tuple_inversion.
have H_q' := @pt_lb_input_handlers_some _ _ _ _ _ _ _ _ multi_map_lb_congr _ _ _ _ _ _ _ _ H_i Heqp1.
break_and.
unfold tot_mapped_lb_input_handlers_label in *.
repeat break_let.
repeat tuple_inversion.
by rewrite /pt_map_net /= tot_map_name_inv_inverse.
*
rewrite /pt_map_net /=.
rewrite filterMap_app filterMap_pt_map_packet_map_eq.
by rewrite -(@pt_map_update_eq _ _ _ _ _ _ name_map_bijective).
