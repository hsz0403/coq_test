Require Import Verdi.Verdi.
Require Import Verdi.LabeledNet.
Require Import Verdi.TotalMapSimulations.
Require Import InfSeqExt.infseq.
Require Import InfSeqExt.map.
Require Import InfSeqExt.exteq.
Require Import FunctionalExtensionality.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import Verdi.Ssrexport.
Set Implicit Arguments.
Class LabeledMultiParamsLabelTotalMap (B0 : BaseParams) (B1 : BaseParams) (P0 : LabeledMultiParams B0) (P1 : LabeledMultiParams B1) := { tot_map_label : @label B0 P0 -> @label B1 P1 }.
Section LabeledTotalMapDefs.
Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {labeled_multi_fst : LabeledMultiParams base_fst}.
Context {labeled_multi_snd : LabeledMultiParams base_snd}.
Context {label_map : LabeledMultiParamsLabelTotalMap labeled_multi_fst labeled_multi_snd}.
Definition tot_mapped_lb_net_handlers_label me src m st := let '(lb, out, st', ps) := lb_net_handlers me src m st in tot_map_label lb.
Definition tot_mapped_lb_input_handlers_label me inp st := let '(lb, out, st', ps) := lb_input_handlers me inp st in tot_map_label lb.
End LabeledTotalMapDefs.
Class LabeledMultiParamsTotalMapCongruency (B0 : BaseParams) (B1 : BaseParams) (P0 : LabeledMultiParams B0) (P1 : LabeledMultiParams B1) (B : BaseParamsTotalMap B0 B1) (N : MultiParamsNameTotalMap (@unlabeled_multi_params _ P0) (@unlabeled_multi_params _ P1)) (P : MultiParamsMsgTotalMap (@unlabeled_multi_params _ P0) (@unlabeled_multi_params _ P1)) (L : LabeledMultiParamsLabelTotalMap P0 P1) : Prop := { tot_lb_net_handlers_eq : forall me src m st out st' ps lb, lb_net_handlers (tot_map_name me) (tot_map_name src) (tot_map_msg m) (tot_map_data st) = (lb, out, st', ps) -> tot_mapped_lb_net_handlers_label me src m st = lb ; tot_lb_input_handlers_eq : forall me inp st out st' ps lb, lb_input_handlers (tot_map_name me) (tot_map_input inp) (tot_map_data st) = (lb, out, st', ps) -> tot_mapped_lb_input_handlers_label me inp st = lb ; tot_lb_label_silent_fst_snd : tot_map_label label_silent = label_silent }.
Section TotalMapExecutionSimulations.
Context {base_fst : BaseParams}.
Context {base_snd : BaseParams}.
Context {labeled_multi_fst : LabeledMultiParams base_fst}.
Context {labeled_multi_snd : LabeledMultiParams base_snd}.
Context {base_map : BaseParamsTotalMap base_fst base_snd}.
Context {name_map : MultiParamsNameTotalMap (@unlabeled_multi_params _ labeled_multi_fst) (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {msg_map : MultiParamsMsgTotalMap (@unlabeled_multi_params _ labeled_multi_fst) (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {label_map : LabeledMultiParamsLabelTotalMap labeled_multi_fst labeled_multi_snd}.
Context {name_map_bijective : MultiParamsNameTotalMapBijective name_map}.
Context {multi_map_congr : MultiParamsTotalMapCongruency base_map name_map msg_map}.
Context {multi_map_lb_congr : LabeledMultiParamsTotalMapCongruency base_map name_map msg_map label_map}.
Hypothesis tot_map_label_injective : forall l l', tot_map_label l = tot_map_label l' -> l = l'.
Definition tot_map_net_event e := {| evt_a := (List.map tot_map_name (fst e.(evt_a)), tot_map_net (snd e.(evt_a))) ; evt_l := tot_map_label e.(evt_l) ; evt_trace := List.map tot_map_trace_occ e.(evt_trace) |}.
Context {fail_fst : FailureParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {fail_snd : FailureParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {fail_map_congr : FailureParamsTotalMapCongruency fail_fst fail_snd base_map}.
Definition tot_map_onet_event e := {| evt_a := (List.map tot_map_name (fst e.(evt_a)), tot_map_onet (snd e.(evt_a))) ; evt_l := tot_map_label e.(evt_l) ; evt_trace := List.map tot_map_trace e.(evt_trace) |}.
Context {overlay_fst : NameOverlayParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {overlay_snd : NameOverlayParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {overlay_map_congr : NameOverlayParamsTotalMapCongruency overlay_fst overlay_snd name_map}.
Context {fail_msg_fst : FailMsgParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {fail_msg_snd : FailMsgParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {fail_msg_map_congr : FailMsgParamsTotalMapCongruency fail_msg_fst fail_msg_snd msg_map}.
Definition tot_map_odnet_event e := {| evt_a := (List.map tot_map_name (fst e.(evt_a)), tot_map_odnet (snd e.(evt_a))) ; evt_l := tot_map_label e.(evt_l) ; evt_trace := List.map tot_map_trace e.(evt_trace) |}.
Context {new_msg_fst : NewMsgParams (@unlabeled_multi_params _ labeled_multi_fst)}.
Context {new_msg_snd : NewMsgParams (@unlabeled_multi_params _ labeled_multi_snd)}.
Context {new_msg_map_congr : NewMsgParamsTotalMapCongruency new_msg_fst new_msg_snd msg_map}.
End TotalMapExecutionSimulations.

Lemma tot_map_onet_label_event_inf_often_occurred_conv : forall l s, inf_often (now (occurred (tot_map_label l))) (map tot_map_onet_event s) -> inf_often (now (occurred l)) s.
Proof using tot_map_label_injective.
move => l.
apply: always_map_conv.
apply: eventually_map_conv => //.
-
rewrite /extensional /=.
case => e s1.
case => e' s2.
move => H_eq.
by inversion H_eq; subst_max.
-
rewrite /extensional /=.
case => e s1.
case => e' s2.
move => H_eq.
by inversion H_eq; subst_max.
-
case => e s.
rewrite /= /occurred /=.
move => H_eq.
exact: tot_map_label_injective.
