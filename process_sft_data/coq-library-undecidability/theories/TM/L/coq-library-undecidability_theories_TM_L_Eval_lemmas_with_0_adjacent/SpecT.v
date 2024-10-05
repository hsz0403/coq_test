From Undecidability Require Import L.Util.L_facts.
From Undecidability.Shared.Libs.PSL Require Import FinTypes Vectors.
Require Import List.
Require Import Undecidability.TM.Util.TM_facts.
From Undecidability Require Import ProgrammingTools LM_heap_def WriteValue CaseList Copy ListTM Hoare.
From Undecidability.TM.L Require Import JumpTargetTM Alphabets M_LHeapInterpreter.
From Undecidability Require Import L.AbstractMachines.FlatPro.LM_heap_correct.
Require Import List.
Import Vector.VectorNotations.
Import ListNotations ResourceMeasures.
From Undecidability.TM.L Require Import UnfoldClos.
Require Import Equations.Prop.DepElim.
Import CasePair Code.CaseList.
Set Default Proof Using "Type".
Module EvalL.
Section Fix.
Variable Σ : finType.
Definition Σintern :Type := sigStep + sigList (sigPair sigHClos sigNat).
Context (retr_eval : Retract Σintern Σ) (retr_pro : Retract sigPro Σ).
Definition retr_unfolder : Retract (sigList (sigPair sigHClos sigNat)) Σ := ComposeRetract retr_eval _.
Definition retr_interpreter : Retract sigStep Σ := ComposeRetract retr_eval _.
Local Instance retr_closs_intrp : Retract (sigList (sigHClos)) Σ := ComposeRetract retr_interpreter _.
Local Instance retr_clos_intrp : Retract sigHClos Σ := ComposeRetract retr_closs_intrp _.
Local Instance retr_pro_intrp : Retract sigPro Σ := ComposeRetract retr_clos_intrp _.
Local Instance retr_nat_clos_ad' : Retract sigNat sigHClos := Retract_sigPair_X _ (Retract_id _).
Local Instance retr_nat_clos_ad : Retract sigNat Σ := ComposeRetract _ retr_nat_clos_ad'.
Local Instance retr_heap : Retract sigHeap Σ := ComposeRetract retr_interpreter _.
Definition M : pTM (Σ^+) unit 11 := Translate retr_pro retr_pro_intrp @ [|Fin0|];; CopyValue _ @ [|Fin0;Fin1|];; Reset _ @[|Fin0|];; WriteValue 0 ⇑ retr_nat_clos_ad @ [| Fin0|];; Constr_pair _ _ ⇑ retr_clos_intrp @ [|Fin0;Fin1|];; Reset _ @ [|Fin0|];; WriteValue ( []%list) ⇑ retr_closs_intrp @ [| Fin0|];; Constr_cons _ ⇑ retr_closs_intrp @ [|Fin0;Fin1|];; Reset _ @ [|Fin1|];; WriteValue ( []%list) ⇑ retr_closs_intrp @ [| Fin1|];; WriteValue ( []%list ) ⇑ retr_heap @ [| Fin2|];; M_LHeapInterpreter.Loop ⇑ retr_interpreter;; Reset _ @ [|Fin0|];; CaseList _ ⇑ retr_closs_intrp @ [| Fin1;Fin0 |];; Reset _ @ [|Fin1|];; UnfoldClos.M retr_unfolder retr_heap retr_clos_intrp @ [| Fin0;Fin2;Fin1;Fin3;Fin4;Fin5;Fin6;Fin7;Fin8;Fin9|];; Reset _ @ [|Fin2|];; Translate (UnfoldClos.retr_pro _) retr_pro @ [|Fin0|].
Arguments "+" : simpl never.
Arguments "*" : simpl never.
Definition steps (s : term) (k:nat) (t:term) Hcl (HR:evalIn k s t):= 1 + Translate_steps (compile s) + (1 + CopyValue_steps (compile s) + (1 + Reset_steps (compile s) + (1 + WriteValue_steps (size 0) + (1 + Constr_pair_steps 0 + (1 + Reset_steps 0 + (1 + WriteValue_steps (size []%list) + (1 + Constr_cons_steps (0, compile s) + (1 + Reset_steps (0, compile s) + (1 + WriteValue_steps (size []%list) + (1 + WriteValue_steps (size []%list) + (1 + Loop_steps [(0, compile s)] [] []%list (3 * k + 1) + (1 + Reset_steps []%list + let (g,tmp) := completenessTimeInformative (proj2 (timeBS_evalIn _ _ _) HR) Hcl in let (H,_):= tmp in (1 + CaseList_steps [g] + (1 + Reset_steps []%list + (1 + UnfoldClos.steps H g t + (1 + Reset_steps H + Translate_steps (compile t))))))))))))))))).
Arguments steps : clear implicits.
End Fix.
End EvalL.

Lemma SpecT s k t (Hcl: closed s) (HR:evalIn k s t): TripleT ≃≃([],[|Contains retr_pro (compile s)|] ++ Vector.const Void _) (steps s k t Hcl HR) M (fun _ => ≃≃([],[|Contains retr_pro (compile t)|] ++ Vector.const Void _)).
Proof.
unfold steps.
destruct completenessTimeInformative as (g&H&?&?).
clear HR.
eapply ConsequenceT_pre.
2:reflexivity.
unfold M.
do 11 (hstep_seq;[]).
cbn.
hstep_seq;[| | ] .
{
refine (TripleT_RemoveSpace _).
intros.
eapply Interpreter_SpecT.
eassumption.
inversion 1.
}
now cbn; tspec_ext.
do 2 (hstep_seq;[]).
hintros _ _.
hstep_seq;[].
hstep_seq;[|].
{
eapply UnfoldClos.SpecT.
eassumption.
}
cbn.
do 2 (hstep_seq;[]).
reflexivity.
unfold steps.
reflexivity.
