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

Lemma pt_map_odnet_tot_map_label_event_inf_often_occurred_conv : forall l s, inf_often (now (occurred (tot_map_label l))) (map pt_map_odnet_event s) -> inf_often (now (occurred l)) s.
Proof using tot_map_label_injective.
move => l.
apply: always_map_conv.
apply: eventually_map_conv => //.
-
exact: extensional_now.
-
exact: extensional_now.
-
case => e s.
rewrite /= /occurred /=.
move => H_eq.
exact: tot_map_label_injective.
