From Undecidability Require Import TM.Code.ProgrammingTools LM_heap_def.
From Undecidability.TM.L Require Import Alphabets CaseCom LookupTM JumpTargetTM.
From Undecidability Require Import TM.Code.ListTM TM.Code.CaseList TM.Code.CasePair TM.Code.CaseSum.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Local Hint Resolve isVoid_isVoid_size : core.
Section StepMachine.
Implicit Types H : Heap.
Implicit Types T V : list HClos.
Implicit Types a b c : HAdd.
Implicit Types g : HClos.
Implicit Types (P Q : Pro).
Variable sigStep : finType.
Variable retr_closures_step : Retract (sigList sigHClos) sigStep.
Variable retr_heap_step : Retract sigHeap sigStep.
Set Default Proof Using "Type".
Local Definition retr_clos_step : Retract sigHClos sigStep := ComposeRetract retr_closures_step _.
Definition retr_pro_clos : Retract sigPro sigHClos := _.
Local Definition retr_pro_step : Retract sigPro sigStep := ComposeRetract retr_clos_step retr_pro_clos.
Local Definition retr_tok_step : Retract sigCom sigStep := ComposeRetract retr_pro_step _.
Local Definition retr_nat_clos_ad : Retract sigNat sigHClos := Retract_sigPair_X _ (Retract_id _).
Local Definition retr_nat_step_clos_ad : Retract sigNat sigStep := ComposeRetract retr_clos_step retr_nat_clos_ad.
Local Definition retr_nat_clos_var : Retract sigNat sigHClos := Retract_sigPair_Y _ _.
Local Definition retr_nat_step_clos_var : Retract sigNat sigStep := ComposeRetract retr_clos_step retr_nat_clos_var.
Local Definition Step_Lookup := Lookup retr_clos_step retr_heap_step.
Definition TailRec_size (T : list HClos) (P : Pro) (a : HAdd) : Vector.t (nat->nat) 3 := match P with | nil => [| id; Reset_size P; id|] | c :: P' => [| (*0*) Constr_cons_size (a,P); (*1*) Constr_pair_size a >> Reset_size (a,P); (*2*) id |] end.
Definition TailRec_Rel : pRel sigStep^+ unit 3 := ignoreParam ( fun tin tout => forall T P a (s0 s1 s2 : nat), tin[@Fin0] ≃(;s0) T -> tin[@Fin1] ≃(retr_pro_step;s1) P -> tin[@Fin2] ≃(retr_nat_step_clos_ad;s2) a -> tout[@Fin0] ≃(;TailRec_size T P a @>Fin0 s0) tailRecursion (a, P) T /\ isVoid_size tout[@Fin1] (TailRec_size T P a @>Fin1 s1) /\ tout[@Fin2] ≃(retr_nat_step_clos_ad; TailRec_size T P a @>Fin2 s2) a ).
Definition TailRec : pTM sigStep^+ unit 3 := If (IsNil sigCom_fin ⇑ retr_pro_step @ [|Fin1|]) (Reset _ @ [|Fin1|]) (Constr_pair sigHAdd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin2; Fin1|];; Constr_cons sigHClos_fin ⇑ _ @ [|Fin0; Fin1|];; Reset _ @ [|Fin1|]).
Local Arguments TailRec_size : simpl never.
Local Arguments tailRecursion : simpl never.
Definition TailRec_steps P a := match P with | nil => 1 + IsNil_steps + Reset_steps nil | t::P => 1 + IsNil_steps + 1 + Constr_pair_steps a + 1 + Constr_cons_steps (a,t::P) + Reset_steps (a, t :: P) end.
Definition TailRec_T : tRel sigStep^+ 3 := fun tin k => exists T P a, tin[@Fin0] ≃ T /\ tin[@Fin1] ≃(retr_pro_step) P /\ tin[@Fin2] ≃(retr_nat_step_clos_ad) a /\ TailRec_steps P a <= k.
Definition ConsClos_size (T : list HClos) (Q : Pro) (a : HAdd) : Vector.t (nat->nat) 3 := [| Constr_cons_size (a,Q); Reset_size a; Constr_pair_size a >> Reset_size (a, Q) |].
Definition ConsClos_Rel : pRel sigStep^+ unit 3 := ignoreParam ( fun tin tout => forall T Q a (s0 s1 s2 : nat), tin[@Fin0] ≃(;s0) T -> tin[@Fin1] ≃(retr_nat_step_clos_ad;s1) a -> tin[@Fin2] ≃(retr_pro_step;s2) Q -> tout[@Fin0] ≃(;ConsClos_size T Q a @>Fin0 s0) (a, Q) :: T /\ isVoid_size tout[@Fin1] (ConsClos_size T Q a @>Fin1 s1) /\ isVoid_size tout[@Fin2] (ConsClos_size T Q a @>Fin2 s2) ).
Definition ConsClos : pTM sigStep^+ unit 3 := Constr_pair sigHAdd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin1; Fin2|];; Constr_cons sigHClos_fin ⇑ _ @ [|Fin0; Fin2|];; Reset _ @ [|Fin2|];; Reset _ @ [|Fin1|].
Local Arguments ConsClos_size : simpl never.
Definition ConsClos_steps Q a := 3 + Constr_pair_steps a + Constr_cons_steps (a,Q) + Reset_steps (a,Q) + Reset_steps a.
Definition ConsClos_T : tRel sigStep^+ 3 := fun tin k => exists T Q a, tin[@Fin0] ≃ T /\ tin[@Fin1] ≃(retr_nat_step_clos_ad) a /\ tin[@Fin2] ≃(retr_pro_step) Q /\ ConsClos_steps Q a <= k.
Definition Step_lam_size (T V : list HClos) (H : Heap) (a : HAdd) (P : Pro) : Vector.t (nat->nat) 10 := match jumpTarget 0 [] P with | Some (Q, P') => (JumpTarget_size P @>> [|Fin3; Fin6; Fin7; Fin8; Fin9|]) >>> (TailRec_size T P' a @>> [|Fin0; Fin3; Fin4|]) >>> (ConsClos_size V Q a @>> [|Fin1; Fin4; Fin6|]) | _ => default end.
Definition Step_lam_Rel : pRel sigStep^+ bool 10 := fun tin '(yout, tout) => forall (T V : list HClos) (H : Heap) (a : HAdd) (P : Pro) (s0 s1 s2 s3 s4 : nat) (sr : Vector.t nat 5), let size := Step_lam_size T V H a P in tin[@Fin0] ≃(;s0) T -> tin[@Fin1] ≃(;s1) V -> tin[@Fin2] ≃(;s2) H -> tin[@Fin3] ≃(retr_pro_step;s3) P -> tin[@Fin4] ≃(retr_nat_step_clos_ad;s4) a -> (forall i : Fin.t 5, isVoid_size tin[@FinR 5 i] sr[@i]) -> match yout with | true => exists (P' Q : Pro), jumpTarget 0 [] P = Some (Q, P') /\ tout[@Fin0] ≃(;size@>Fin0 s0) tailRecursion (a, P') T /\ tout[@Fin1] ≃(;size@>Fin1 s1) (a, Q) :: V /\ tout[@Fin2] ≃(;size@>Fin2 s2) H /\ (forall i : Fin.t 7, isVoid_size tout[@FinR 3 i] (size@>(FinR 3 i) (s3:::s4:::sr)[@i])) | false => jumpTarget 0 [] P = None end.
Definition Step_lam : pTM sigStep^+ bool 10 := If (JumpTarget ⇑ retr_pro_step @ [|Fin3; Fin6; Fin7; Fin8; Fin9|]) (Return (TailRec @ [|Fin0; Fin3; Fin4|];; ConsClos @ [|Fin1; Fin4; Fin6|]) true) (Return Nop false).
Definition Step_lam_steps_JumpTarget P a := match jumpTarget 0 [] P with | Some (Q', P') => 1 + TailRec_steps P' a + ConsClos_steps Q' a | None => 0 end.
Definition Step_lam_steps P a := 1 + JumpTarget_steps P + Step_lam_steps_JumpTarget P a.
Definition Step_lam_T : tRel sigStep^+ 10 := fun tin k => exists (T V : list HClos) (H : Heap) (a : HAdd) (P : Pro), tin[@Fin0] ≃ T /\ tin[@Fin1] ≃ V /\ tin[@Fin2] ≃ H /\ tin[@Fin3] ≃(retr_pro_step) P /\ tin[@Fin4] ≃(retr_nat_step_clos_ad) a /\ (forall i : Fin.t 5, isVoid tin[@FinR 5 i]) /\ Step_lam_steps P a <= k.
Definition Put_size (H : Heap) (g : HClos) (b : HAdd) : Vector.t (nat->nat) 6 := (* (Length_size H @>> [|Fin0; Fin3; Fin4; Fin5|]) >>> ([|pred|] @>> [|Fin4|]) >>> (* nil *) ([|Constr_pair_size g >> pred|] @>>[|Fin2|]) >>> (* pair and [Some] on tape 2 *) ... *) [| (*0*) Length_size H @>Fin0 >> MoveValue_size_y (H++[Some(g,b)]) H; (*1*) Reset_size g; (*2*) Constr_pair_size g >> pred >> Reset_size (Some(g,b)); (*3*) Length_size H @>Fin1; (*4*) Length_size H @>Fin2 >> pred >> Constr_cons_size (Some(g,b)) >> App'_size H >> MoveValue_size_x (H++[Some(g,b)]); (* nil and cons *) (*5*) Length_size H @>Fin3 |].
Definition Put_Rel : pRel sigStep^+ unit 6 := ignoreParam ( fun tin tout => forall (H : Heap) (g : HClos) (b : HAdd) (s0 s1 s2 s3 s4 s5 : nat), let size := Put_size H g b in tin[@Fin0] ≃(;s0) H -> tin[@Fin1] ≃(retr_clos_step;s1) g -> tin[@Fin2] ≃(retr_nat_step_clos_ad;s2) b -> isVoid_size tin[@Fin3] s3 -> isVoid_size tin[@Fin4] s4 -> isVoid_size tin[@Fin5] s5 -> tout[@Fin0] ≃(;size @>Fin0 s0) H ++ [Some (g,b)] /\ isVoid_size tout[@Fin1] (size @>Fin1 s1) /\ isVoid_size tout[@Fin2] (size @>Fin2 s2) /\ tout[@Fin3] ≃(retr_nat_step_clos_ad; size @>Fin3 s3) length H /\ isVoid_size tout[@Fin4] (size @>Fin4 s4) /\ isVoid_size tout[@Fin5] (size @>Fin5 s5) ).
Local Definition retr_nat_step_hent : Retract sigNat sigStep := ComposeRetract retr_heap_step retr_nat_heap_entry.
Local Definition retr_clos_step_hent : Retract sigHClos sigStep := ComposeRetract retr_heap_step retr_clos_heap.
Local Definition retr_hent'_step : Retract sigHEntr' sigStep := ComposeRetract retr_heap_step retr_hent'_heap.
Local Definition retr_hent_step : Retract sigHEntr sigStep := ComposeRetract retr_heap_step retr_hent_heap.
Definition Put : pTM sigStep^+ unit 6 := Length retr_heap_step retr_nat_step_clos_ad @ [|Fin0; Fin3; Fin4; Fin5|];; Constr_nil HEntr ⇑ _ @ [|Fin4|];; Translate retr_nat_step_clos_ad retr_nat_step_hent @ [|Fin2|];; Translate retr_clos_step retr_clos_step_hent @ [|Fin1|];; Constr_pair sigHClos_fin sigHAdd_fin ⇑ retr_hent'_step @ [|Fin1; Fin2|];; Constr_Some sigHEntr'_fin ⇑ retr_hent_step @ [|Fin2|];; Constr_cons sigHEntr_fin ⇑ _ @ [|Fin4; Fin2|];; App' sigHEntr_fin ⇑ _ @ [|Fin0; Fin4|];; MoveValue _ @ [|Fin4; Fin0|];; Reset _ @ [|Fin2|];; Reset _ @ [|Fin1|].
Local Arguments Put_size : simpl never.
Definition Put_steps H g b := 10 + Length_steps H + Constr_nil_steps + Translate_steps b + Translate_steps g + Constr_pair_steps g + Constr_Some_steps + Constr_cons_steps (Some (g, b)) + App'_steps H + MoveValue_steps (H++[Some(g,b)]) H + Reset_steps (Some (g, b)) + Reset_steps g.
Definition Put_T : tRel sigStep ^+ 6 := fun tin k => exists (H : Heap) (g : HClos) (b : HAdd), tin[@Fin0] ≃ H /\ tin[@Fin1] ≃(retr_clos_step) g /\ tin[@Fin2] ≃(retr_nat_step_clos_ad) b /\ isVoid tin[@Fin3] /\ isVoid tin[@Fin4] /\ isVoid tin[@Fin5] /\ Put_steps H g b <= k.
Definition Step_app_size (T V : list HClos) (H : Heap) (a : HAdd) (P : Pro) : Vector.t (nat->nat) 11 := match V with | g :: (b, Q) :: V' => ([|CaseList_size0 g; CaseList_size1 g|] @>> [|Fin1;Fin5|]) >>> ([|CaseList_size0 (b,Q); CaseList_size1 (b,Q)|] @>> [|Fin1;Fin6|]) >>> ([|CasePair_size0 b; CasePair_size1 b|] @>> [|Fin6;Fin7|]) >>> (TailRec_size T P a @>> [|Fin0; Fin3; Fin4|]) >>> ([|Reset_size a|] @>> [|Fin4|]) >>> (Put_size H g b @>> [|Fin2; Fin5; Fin7; Fin8; Fin9; Fin10|]) >>> (ConsClos_size (tailRecursion (a,P) T) Q (length H) @>> [|Fin0; Fin8; Fin6|]) | _ => default (* not specified *) end.
Definition Step_app_Rel : pRel sigStep^+ bool 11 := fun tin '(yout, tout) => forall (T V : list HClos) (H : Heap) (a : HAdd) (P : Pro) (s0 s1 s2 s3 s4 : nat) (sr : Vector.t nat 6), let size := Step_app_size T V H a P in tin[@Fin0] ≃(;s0) T -> tin[@Fin1] ≃(;s1) V -> tin[@Fin2] ≃(;s2) H -> tin[@Fin3] ≃(retr_pro_step;s3) P -> tin[@Fin4] ≃(retr_nat_step_clos_ad;s4) a -> (forall i : Fin.t 6, isVoid_size tin[@FinR 5 i] sr[@i]) -> match yout, V with | true, g :: (b, Q) :: V => let (c, H') := put H (Some (g, b)) in (* This simplifys immediatly by computation *) tout[@Fin0] ≃(;size@>Fin0 s0) (c, Q) :: tailRecursion (a, P) T /\ tout[@Fin1] ≃(;size@>Fin1 s1) V /\ tout[@Fin2] ≃(;size@>Fin2 s2) H' /\ (forall i : Fin.t 8, isVoid_size tout[@FinR 3 i] (size @>(FinR 3 i) (s3:::s4:::sr)[@i])) | false, [] => True | false, [_] => True | _, _ => False end.
Definition Step_app : pTM sigStep^+ bool 11 := If (CaseList sigHClos_fin ⇑ _ @ [|Fin1; Fin5|]) (If (CaseList sigHClos_fin ⇑ _ @ [|Fin1; Fin6|]) (Return (CasePair sigHAdd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin6; Fin7|];; TailRec @ [|Fin0; Fin3; Fin4|];; Reset _ @ [|Fin4|];; Put @ [|Fin2; Fin5; Fin7; Fin8; Fin9; Fin10|];; ConsClos @ [|Fin0; Fin8; Fin6|]) (true)) (Return Nop false)) (Return Nop false) .
Arguments Step_app_size : simpl never.
Arguments Step_app_size : simpl never.
Definition Step_app_steps_CaseList' g V' H P a := match V' with | nil => 0 (* Nop *) | (b, Q) :: V'' => 4 + CasePair_steps b + TailRec_steps P a + Reset_steps a + Put_steps H g b + ConsClos_steps Q (length H) end.
Definition Step_app_steps_CaseList V H P a := match V with | nil => 0 (* Nop *) | g :: V' => 1 + CaseList_steps V' + Step_app_steps_CaseList' g V' H P a end.
Definition Step_app_steps V H a P := 1 + CaseList_steps V + Step_app_steps_CaseList V H P a.
Definition Step_app_T : tRel sigStep^+ 11 := fun tin k => exists (T V : list HClos) (H : Heap) (P : Pro) (a : HAdd), tin[@Fin0] ≃ T /\ tin[@Fin1] ≃ V /\ tin[@Fin2] ≃ H /\ tin[@Fin3] ≃(retr_pro_step) P /\ tin[@Fin4] ≃(retr_nat_step_clos_ad) a /\ (forall i : Fin.t 6, isVoid tin[@FinR 5 i]) /\ Step_app_steps V H a P <= k.
Definition Step_var_size (T V : list HClos) (H : Heap) (a : HAdd) (n : nat) (P : Pro) : Vector.t (nat->nat) 8 := match lookup H a n with | Some g => (TailRec_size T P a @>> [|Fin0; Fin3; Fin4|]) >>> (Lookup_size H a n @>> [|Fin2; Fin4; Fin5; Fin6; Fin7|]) >>> ([|Constr_cons_size g; Reset_size g|] @>> [|Fin1; Fin6|]) | None => default end.
Definition Step_var_Rel : pRel sigStep^+ bool 8 := fun tin '(yout, tout) => forall (T V : list HClos) (H : Heap) (a : HAdd) (n : nat) (P : Pro) (s0 s1 s2 s3 s4 s5 s6 s7 : nat), let size := Step_var_size T V H a n P in tin[@Fin0] ≃(;s0) T -> tin[@Fin1] ≃(;s1) V -> tin[@Fin2] ≃(;s2) H -> tin[@Fin3] ≃(retr_pro_step;s3) P -> tin[@Fin4] ≃(retr_nat_step_clos_ad;s4) a -> tin[@Fin5] ≃(retr_nat_step_clos_var;s5) n -> isVoid_size tin[@Fin6] s6 -> isVoid_size tin[@Fin7] s7 -> match yout with | true => exists (g : HClos), lookup H a n = Some g /\ tout[@Fin0] ≃(;size@>Fin0 s0) tailRecursion (a, P) T /\ tout[@Fin1] ≃(;size@>Fin1 s1) g :: V /\ tout[@Fin2] ≃(;size@>Fin2 s2) H /\ (forall i : Fin.t 5, isVoid_size tout[@FinR 3 i] (size @>(FinR 3 i) [|s3;s4;s5;s6;s7|][@i])) | false => lookup H a n = None end .
Definition Step_var : pTM sigStep^+ bool 8 := TailRec @ [|Fin0; Fin3; Fin4|];; If (Step_Lookup @ [|Fin2; Fin4; Fin5; Fin6; Fin7|]) (Return (Constr_cons sigHClos_fin ⇑ _ @ [|Fin1; Fin6|];; Reset _ @ [|Fin6|]) (true)) (Return Nop false).
Local Definition retr_closure_step : Retract sigHClos sigStep := ComposeRetract retr_closures_step _.
Local Arguments Step_var_size : simpl never.
Definition Step_var_steps_Lookup H a n := match lookup H a n with | None => 0 (* Nop *) | Some g => 1 + Constr_cons_steps g + Reset_steps g end.
Definition Step_var_steps P H a n := 2 + TailRec_steps P a + Lookup_steps H a n + Step_var_steps_Lookup H a n.
Definition Step_var_T : tRel sigStep^+ 8 := fun tin k => exists (T V : list HClos) (H : Heap) (a : HAdd) (n : nat) (P : Pro), tin[@Fin0] ≃ T /\ tin[@Fin1] ≃ V /\ tin[@Fin2] ≃ H /\ tin[@Fin3] ≃(retr_pro_step) P /\ tin[@Fin4] ≃(retr_nat_step_clos_ad) a /\ tin[@Fin5] ≃(retr_nat_step_clos_var) n /\ isVoid tin[@Fin6] /\ isVoid tin[@Fin7] /\ Step_var_steps P H a n <= k.
Local Coercion bool2optunit := fun b : bool => if b then None else Some tt.
Definition Step : pTM sigStep^+ (option unit) 11 := Relabel (If (CaseList sigHClos_fin ⇑ _ @ [|Fin0; Fin3|]) (CasePair sigHAdd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin3; Fin4|];; If (CaseList sigCom_fin ⇑ retr_pro_step @ [|Fin3; Fin5|]) (Switch (CaseCom ⇑ retr_tok_step @ [|Fin5|]) (fun t : option ACom => match t with | Some lamAT => Step_lam @ [|Fin0; Fin1; Fin2; Fin3; Fin4; Fin5; Fin6; Fin7; Fin8; Fin9|] | Some appAT => Step_app | Some retAT => Return Nop false | None (* Variable *) => Step_var @ [|Fin0; Fin1; Fin2; Fin3; Fin4; Fin5; Fin6; Fin7|] end)) (Return Nop false)) (Return Nop false) ) bool2optunit.
Definition Step_size (T V : list HClos) (H : Heap) : Vector.t (nat->nat) 11 := match T with | (a, (t :: P)) :: T' => (* Common steps: destruct [T] (on tapes 0, 3, 4, 5) *) ([| (*0*) CaseList_size0 (a, (t::P)); (*3*) CaseList_size1 (a, (t::P)) >> CasePair_size0 a >> CaseList_size0 t; (*4*) CasePair_size1 a; (*5*) CaseList_size1 t >> CaseCom_size t |] @>> [|Fin0; Fin3; Fin4; Fin5|]) >>> (match t with | lamT => Step_lam_size T' V H a P @>> [|Fin0; Fin1; Fin2; Fin3; Fin4; Fin5; Fin6; Fin7; Fin8; Fin9|] | appT => Step_app_size T' V H a P | retT => default (* not specified *) | varT n => Step_var_size T' V H a n P @>> [|Fin0; Fin1; Fin2; Fin3; Fin4; Fin5; Fin6; Fin7|] end) | _ => Vector.const id _ end.
Definition Step_Rel : pRel sigStep^+ (option unit) 11 := fun tin '(yout, tout) => forall (T V : list HClos) (H: Heap) (s0 s1 s2 : nat) (sr : Vector.t nat 8), let size := Step_size T V H in tin[@Fin0] ≃(;s0) T -> tin[@Fin1] ≃(;s1) V -> tin[@Fin2] ≃(;s2) H -> (forall i : Fin.t 8, isVoid_size tin[@FinR 3 i] (sr[@i])) -> match yout with | None => exists T' V' H', step (T,V,H) (T',V',H') /\ tout[@Fin0] ≃(;size@>Fin0 s0) T' /\ tout[@Fin1] ≃(;size@>Fin1 s1) V' /\ tout[@Fin2] ≃(;size@>Fin2 s2) H' /\ (forall i : Fin.t 8, isVoid_size tout[@FinR 3 i] (size@>(FinR 3 i) sr[@i])) | Some tt => halt_state (T,V,H) /\ match T with | nil => tout[@Fin0] ≃(;size@>Fin0 s0) (@nil HClos) /\ tout[@Fin1] ≃(;size@>Fin1 s1) V /\ tout[@Fin2] ≃(;size@>Fin2 s2) H /\ (forall i : Fin.t 8, isVoid_size tout[@FinR 3 i] (size@>(FinR 3 i) sr[@i])) | _ => True end end.
Arguments Step_size : simpl never.
Opaque Step_app_size.
Global Arguments Step_size : simpl never.
Definition Step_steps_CaseCom a t P' V H := match t with | varT n => Step_var_steps P' H a n | appT => Step_app_steps V H a P' | lamT => Step_lam_steps P' a | retT => 0 (* Nop *) end.
Definition Step_steps_CaseList' a P V H := match P with | nil => 0 | t :: P' => 1 + CaseCom_steps + Step_steps_CaseCom a t P' V H end.
Definition Step_steps_CaseList T V H := match T with | nil => 0 | (a,P) :: T' => 2 + CasePair_steps a + CaseList_steps P + Step_steps_CaseList' a P V H end.
Definition Step_steps T V H := 1 + CaseList_steps T + Step_steps_CaseList T V H.
Definition Step_T : tRel sigStep^+ 11 := fun tin k => exists (T V : list HClos) (H: Heap), tin[@Fin0] ≃ T /\ tin[@Fin1] ≃ V /\ tin[@Fin2] ≃ H /\ (forall i : Fin.t 8, isVoid tin[@FinR 3 i]) /\ Step_steps T V H <= k.
End StepMachine.

Lemma Step_app_Realise : Step_app ⊨ Step_app_Rel.
Proof.
eapply Realise_monotone.
{
unfold Step_app.
TM_Correct.
-
apply TailRec_Realise.
-
apply Put_Realise.
-
apply ConsClos_Realise.
}
{
intros tin (yout, tout) H.
cbn.
intros T V heap a P s0 s1 s2 s3 s4 sr HEncT HEncV HEncH HEncP HEncA HInt.
TMSimp.
rename H into HIf.
destruct HIf; TMSimp.
{
rename H into HCaseList, H0 into HIf'.
specialize (HInt Fin0) as ?.
specialize (HInt Fin1) as ?.
specialize (HInt Fin2) as ?.
specialize (HInt Fin3) as ?.
specialize (HInt Fin4) as ?.
specialize (HInt Fin5) as ?.
clear HInt.
cbn in *.
modpon HCaseList.
destruct V as [ | g V']; auto; modpon HCaseList.
destruct HIf'; TMSimp.
{
rename H5 into HCaseList'; rename H7 into HCasePair; rename H9 into HTailRec; rename H11 into HReset; rename H13 into HPut; rename H15 into HConsClos.
modpon HCaseList'.
cbn in *.
destruct V' as [ | (b, Q) V'']; auto.
modpon HCaseList'.
specialize (HCasePair (b,Q)).
modpon HCasePair.
cbn in *.
modpon HTailRec.
modpon HReset.
modpon HPut.
modpon HConsClos.
repeat split; auto.
-
intros i; destruct_fin i; cbn; auto; TMSimp_goal; auto.
}
{
modpon H5.
destruct V'; auto.
}
}
{
specialize (HInt Fin0).
modpon H.
destruct V; auto.
}
}
