From Undecidability Require Import ProgrammingTools LM_heap_def.
From Undecidability.TM.L Require Import Alphabets HeapInterpreter.StepTM.
From Undecidability Require Import TM.TM.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Definition sigStep : Type := sigList sigHClos + sigHeap.
Definition retr_heap_step : Retract sigHeap sigStep := _.
Definition retr_closures_step : Retract (sigList sigHClos) sigStep := _.
Definition Loop := While (Step retr_closures_step retr_heap_step).
Local Arguments step_fun : simpl never.
Local Arguments is_halt_state : simpl never.
Local Arguments Step_size : simpl never.
Fixpoint Loop_size (T V : list HClos) (H : Heap) (k : nat) {struct k} : Vector.t (nat->nat) 11 := match k with | 0 => Step_size T V H | S k' => match step_fun (T, V, H) with | Some (T',V',H') => if is_halt_state (T',V',H') then Step_size T V H >>> Step_size T' V' H' else Step_size T V H >>> Loop_size T' V' H' k' | _ => Step_size T V H end end.
Import LM_heap_def.
Definition Loop_Rel : pRel sigStep^+ unit 11 := ignoreParam ( fun tin tout => forall (T V : list HClos) (H: Heap) (s0 s1 s2 : nat) (sr : Vector.t nat 8), tin[@Fin0] ≃(;s0) T -> tin[@Fin1] ≃(;s1) V -> tin[@Fin2] ≃(;s2) H -> (forall i : Fin.t 8, isVoid_size tin[@FinR 3 i] sr[@i]) -> exists T' V' H' (k : nat), let size := Loop_size T V H k in steps_k k (T,V,H) (T',V',H') /\ halt_state (T',V',H') /\ match T' with | nil => tout[@Fin0] ≃(; size @> Fin0 s0) @nil HClos /\ tout[@Fin1] ≃(; size @> Fin1 s1) V' /\ tout[@Fin2] ≃(; size @> Fin2 s2) H' /\ (forall i : Fin.t 8, isVoid_size tout[@FinR 3 i] (size @>(FinR 3 i) sr[@i])) | _ => True end ).
Fixpoint Loop_steps T V H k := match k with | 0 => Step_steps T V H | S k' => match step_fun (T, V, H) with | Some (T',V',H') => if is_halt_state (T',V',H') then 1 + Step_steps T V H + Step_steps T' V' H' else 1 + Step_steps T V H + Loop_steps T' V' H' k' | None => Step_steps T V H end end.
Definition Loop_T : tRel sigStep^+ 11 := fun tin i => exists T V H k, halts_k (T,V,H) k /\ tin[@Fin0] ≃ T /\ tin[@Fin1] ≃ V /\ tin[@Fin2] ≃ H /\ (forall i : Fin.t 8, isVoid tin[@FinR 3 i]) /\ Loop_steps T V H k <= i.
Definition initTapes : state -> tapes sigStep^+ 11 := fun '(T,V,H) => initValue _ _ T ::: initValue _ _ V ::: initValue _ _ H ::: Vector.const (initRight _) 8.
Import Hoare.

Lemma Loop_Terminates : projT1 Loop ↓ Loop_T.
Proof.
eapply TerminatesIn_monotone.
{
unfold Loop.
TM_Correct.
-
apply Step_Realise.
-
apply Step_Terminates.
}
{
eapply WhileCoInduction.
intros tin i.
intros (T&V&Heap&k&Halt&HEncT&HEncV&HEncH&HInt&Hi).
exists (Step_steps T V Heap).
repeat split.
{
hnf.
do 3 eexists; repeat split; eauto.
}
intros ymid tmid HStep.
cbn in HStep.
modpon HStep.
{
instantiate (1 := [| _;_;_;_;_;_;_;_|]).
intros i0.
specialize HInt with (i := i0).
isVoid_mono; cbn.
destruct_fin i0; cbn; constructor.
}
destruct ymid as [ () | ].
-
destruct HStep as (HStep&_).
destruct Halt as (((T'&V')&H')&HSteps&HTerm).
pose proof (halt_state_steps_k HStep HSteps) as (H&->); inv H.
cbn in *.
assumption.
-
destruct HStep as (T1&V1&Heap1&HStep); modpon HStep.
destruct Halt as (((T2&V2)&H2)&HSteps&HTerm).
unfold Loop_T; cbn.
destruct k.
+
inv HSteps.
exfalso.
eapply HTerm; eauto.
+
eapply pow_add with (n:=1) in HSteps as (?&H%rcomp_1&?).
pose proof (step_functional HStep H) as <-.
cbn -[step_fun] in *.
rewrite (step_step_fun HStep) in Hi.
move HTerm at bottom.
clear H.
rename H0 into HSteps.
destruct (is_halt_state (T1, V1, Heap1)) eqn:EHalt.
*
apply is_halt_state_correct in EHalt.
pose proof (halt_state_steps_k EHalt HSteps) as (H&->); inv H.
exists (Step_steps T1 V1 Heap1).
split.
--
do 3 eexists.
eexists 0.
cbn -[step_fun].
repeat split; eauto.
++
econstructor; eauto.
++
intros i0.
specialize HStep3 with (i := i0).
isVoid_mono.
--
lia.
*
exists (Loop_steps T1 V1 Heap1 k).
split.
--
do 3 eexists.
exists k.
repeat split; eauto.
++
econstructor; eauto.
++
intros i0.
specialize HStep3 with (i := i0).
isVoid_mono.
--
lia.
}
