Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Require Import Vector List.
Require Import Undecidability.TM.Util.TM_facts.
From Undecidability Require Import ProgrammingTools WriteValue Copy ListTM JumpTargetTM WriteValue.
From Undecidability.TM.L Require Import Alphabets LookupTM.
From Undecidability.L.AbstractMachines.FlatPro Require Import LM_heap_def LM_heap_correct UnfoldClos.
From Undecidability.TM Require Import CaseList CasePair CaseCom CaseNat NatSub.
From Undecidability Require Import L.L TM.TM Hoare.
From Undecidability.L.Prelim Require Import LoopSum.
Require Import Ring Arith.
Import VectorNotations.
Import ListNotations.
Import Coq.Init.Datatypes List.
Open Scope string_scope.
Require Import String.
Set Default Proof Using "Type".
From Undecidability Require Cons_constant.
Require Import Equations.Prop.DepElim.
Module Private_UnfoldClos.
Section Fix.
Variable Σ : finType.
Variable retr_stack : Retract (sigList (sigPair sigHClos sigNat)) Σ.
Variable retr_heap : Retract sigHeap Σ.
Definition retr_clos : Retract sigHClos Σ := ComposeRetract retr_stack _.
Definition retr_pro : Retract sigPro Σ := ComposeRetract retr_clos _.
Definition retr_com : Retract sigCom Σ := ComposeRetract retr_pro _.
Definition retr_nat_clos_ad' : Retract sigNat sigHClos := Retract_sigPair_X _ _.
Definition retr_nat_clos_ad : Retract sigNat Σ := ComposeRetract retr_clos retr_nat_clos_ad'.
Definition retr_nat_clos_var' : Retract sigNat sigHClos := Retract_sigPair_Y _ _.
Definition retr_nat_clos_var : Retract sigNat Σ := ComposeRetract retr_clos retr_nat_clos_var'.
Definition retr_stackEl : Retract (sigPair sigHClos sigNat) Σ := (ComposeRetract retr_stack _).
Definition retr_nat_stack : Retract sigNat Σ := ComposeRetract retr_stackEl (Retract_sigPair_Y _ _) .
Local Definition Lookup := Lookup retr_clos retr_heap.
Local Notation i_H := Fin0 (only parsing).
Local Notation i_a := Fin1 (only parsing).
Local Notation i_P := Fin2 (only parsing).
Local Notation i_k := Fin3 (only parsing).
Local Notation i_stack' := Fin4 (only parsing).
Local Notation i_res := Fin5 (only parsing).
Local Notation i_aux1 := Fin6 (only parsing).
Local Notation i_aux2 := Fin7 (only parsing).
Local Notation i_aux3 := Fin8 (only parsing).
Local Notation i_aux4 := Fin9 (only parsing).
Definition M__step : pTM (Σ) ^+ (option unit) 10 := If (CaseList _ ⇑ retr_pro @ [| i_P;i_aux1|]) (Switch (CaseCom ⇑ retr_com @ [|i_aux1|]) (fun i : option ACom=> match i with | Some c => Cons_constant.M (ACom2Com c)⇑ retr_pro @ [| i_res|];; Return match c return match c with _ => _ end with | retAT => (CaseNat ⇑ retr_nat_clos_var @ [|i_k|];;Return Nop tt) | lamAT => Constr_S ⇑ retr_nat_clos_var @ [|i_k|] | appAT => Nop end None | None (*var*) => CopyValue _ @ [| i_k;i_aux2|];; CopyValue _ @ [| i_aux1;i_aux3|];; If (Subtract ⇑ retr_nat_clos_var @ [|i_aux3;i_aux2|]) (Reset _ @ [|i_aux1|];; CopyValue _ @ [| i_a;i_aux4|];; If (Lookup @ [|i_H;i_aux4;i_aux3;i_aux1;i_aux2|]) (Cons_constant.M lamT⇑ retr_pro @ [| i_res|];; Cons_constant.M retT⇑ retr_pro @ [| i_P|];; Constr_S ⇑ retr_nat_clos_var @ [|i_k|];; Constr_pair _ _ ⇑ retr_clos @ [|i_a;i_P|];; Reset _ @ [|i_a|];; Translate retr_nat_clos_var retr_nat_stack @[|i_k|];; Constr_pair _ _ ⇑ retr_stackEl @ [|i_P;i_k|];; MoveValue _ @ [|i_aux1;i_P|];; Constr_cons _ ⇑ retr_stack @ [| i_stack';i_k|];; Reset _ @ [|i_k|];; CasePair _ _ ⇑ retr_clos @ [|i_P;i_a|];; Return (WriteValue ( 1) ⇑ retr_nat_clos_var @ [|i_k|]) None ) (Return Diverge (Some tt)) ) (Return (Constr_varT ⇑ retr_com @ [|i_aux1|];; Constr_cons _ ⇑ retr_pro @ [| i_res;i_aux1|];; Reset _ @ [|i_aux1|];; Reset _ @ [|i_aux3|]) None) end) ) ( Reset _ @ [|i_P|];; Reset _ @ [|i_a|];; Reset _ @ [|i_k|];; If (CaseList _ ⇑ retr_stack @ [| i_stack';i_k|]) (CasePair _ _ ⇑ retr_stackEl @ [|i_k;i_P|];; CasePair _ _ ⇑ retr_clos @ [|i_P;i_a|];; Translate retr_nat_stack retr_nat_clos_var @[|i_k|];; Return Nop None ) (Reset _ @ [|i_stack'|];;Return Nop (Some tt)) ).
Local Arguments "+"%nat : simpl never.
Local Arguments "*"%nat : simpl never.
Local Arguments UpToC.f__UpToC {_ _} _ _.
Definition steps_step H (stack : list (HAdd * list Tok * nat)) := match stack with (a,P,k)::stack' => 1 + CaseList_steps P + (if match P with | [] => false | _ :: _ => true end then match P with | [] => 0 | t :: P0 => match t with | varT n => 1 + CaseCom_steps + (1 + CopyValue_steps k + (1 + CopyValue_steps n + (1 + UpToC.f__UpToC (projT1 Subtract_SpecT) k + (if k <=? n then 1 + Reset_steps n + (1 + CopyValue_steps a + match lookup H a (n - k) with | Some h => let (_, _) := h in Lookup_steps H a (n - k) + Cons_constant.time lamT + Cons_constant.time retT + Constr_S_steps + Constr_pair_steps a + Reset_steps a + Translate_steps (1 + k) + Constr_pair_steps (a, retT :: P0) + MoveValue_steps h (a, retT :: P0) + Constr_cons_steps (a, retT :: P0, 1 + k) + Reset_steps (a, retT :: P0, 1 + k) + CasePair_steps (fst h) + WriteValue_steps 2 + Pos.to_nat 11 + 1 | None => 0 end) else Constr_varT_steps + Constr_cons_steps t + Reset_steps t + Reset_steps (n - k) + Pos.to_nat 3)))) | _ => 1 + CaseCom_steps + 16 end end else 1 + Reset_steps P + (1 + Reset_steps a + (1 + Reset_steps k + (1 + CaseList_steps stack' + (if match stack' with | [] => false | _ :: _ => true end then match stack' with | [] => 0 | p :: _ => let (p0, _) := p in let (_, _) := p0 in 1 + CasePair_steps (fst p) + (1 + CasePair_steps (fst p0) + (1 + Translate_steps (snd p) + 0)) end else match stack' with | [] => 1 + Reset_steps stack' + 0 | _ :: _ => 0 end))))) | _ => 0 end.
Arguments steps_step : simpl never.
Definition M__loop := While M__step.
Local Arguments unfoldTailRecStep : simpl never.
Fixpoint steps_loop H n x := match n with 0 => 0 | S n => 1 + steps_step H (fst x) + match unfoldTailRecStep H x with inl y=> steps_loop H n y | inr y=> 0 end end.
Set Keyed Unification.
Definition M := WriteValue ( []) ⇑ retr_stack @ [|i_stack'|];; WriteValue ( []) ⇑ retr_pro @ [|i_res|];; M__loop.
Definition steps H a k s s' := 2 * WriteValue_steps 1 + steps_loop H (L_facts.size s' * 3 + 2) ([(a, compile s, k)], []) + 2.
End Fix.
End Private_UnfoldClos.
Module UnfoldClos.
Section Fix.
Variable Σ : finType.
Variable retr_stack : Retract (sigList (sigPair sigHClos sigNat)) Σ.
Variable retr_heap : Retract sigHeap Σ.
Variable retr_clos : Retract sigHClos Σ.
Definition retr_pro : Retract sigPro Σ := ComposeRetract retr_clos _.
Definition retr_clos_stack : Retract sigHClos Σ := ComposeRetract retr_stack _.
Definition retr_stackEl : Retract (sigPair sigHClos sigNat) Σ := (ComposeRetract retr_stack _).
Definition retr_nat_stack : Retract sigNat Σ := ComposeRetract retr_stackEl (Retract_sigPair_Y _ _) .
Local Notation n := 10 (only parsing).
Local Notation i_io := Fin0 (only parsing).
Local Notation i_H := Fin1 (only parsing).
Definition M : pTM (Σ) ^+ unit n:= Translate retr_clos retr_clos_stack @[|i_io|];; CasePair _ _ ⇑ retr_clos_stack @ [|i_io;Fin2|];; WriteValue ( 1) ⇑ Private_UnfoldClos.retr_nat_clos_var retr_stack @ [|Fin3|];; Private_UnfoldClos.M retr_stack retr_heap @ [|i_H;Fin2;i_io;Fin3;Fin4;Fin5;Fin6;Fin7;Fin8;Fin9|];; Translate (Private_UnfoldClos.retr_pro retr_stack) retr_pro @ [|Fin5|];; WriteValue ( [retT]) ⇑ retr_pro @ [|i_io|];; Rev_Append _ ⇑ retr_pro @ [| Fin5;i_io;Fin6 |];; Cons_constant.M lamT ⇑ retr_pro @ [| i_io|].
Definition steps H '(a',P) t' := match t' with lam t' => match decompile 0 P [] with inl [s'] => 1 + Translate_steps (a', compile s') + (1 + CasePair_steps (fst (a', compile s')) + (1 + WriteValue_steps (size 1) + (1 + Private_UnfoldClos.steps H a' 1 s' t' + (1 + Translate_steps (rev (compile t')) + (1 + WriteValue_steps (size [retT]) + (1 + Rev_Append_steps Encode_Com (rev (compile t')) + Cons_constant.time lamT)))))) | _ => 0 end | _ => 0 end.
End Fix.
End UnfoldClos.

Lemma SpecT (H:Heap) g s: reprC H g s -> TripleT ≃≃([] ,[|Contains retr_clos g;Contains retr_heap H;Void;Void;Void;Void;Void;Void;Void;Void|]) (steps H g s) M (fun r => ≃≃([] ,[|Contains retr_pro (compile s);Contains retr_heap H;Void;Void;Void;Void;Void;Void;Void;Void|])).
Proof.
unfold steps.
intros (s'&t'&a'&Hg&Hs&Hunf)%reprC_elim_deep.
remember (compile s) as P.
subst g s.
rewrite decompile_correct.
unfold M.
eapply ConsequenceT.
2:reflexivity.
do 3 hstep_seq;[].
hstep_seq;[|].
{
hsteps_cbn;cbn.
eapply ConsequenceT_pre.
now refine (Private_UnfoldClos.SpecT _ _ Hunf).
now tspec_ext.
reflexivity.
}
cbn.
do 3 (hstep_seq;[]).
hsteps_cbn.
now tspec_ext.
{
intro;cbn.
tspec_ext.
f_equal.
rewrite rev_involutive.
now subst.
}
reflexivity.
