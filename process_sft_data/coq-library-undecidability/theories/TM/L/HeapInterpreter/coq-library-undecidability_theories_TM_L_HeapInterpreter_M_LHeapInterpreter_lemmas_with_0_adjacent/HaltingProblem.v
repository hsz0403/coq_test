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

Theorem HaltingProblem s : halts s <-> HaltsTM (projT1 Loop) (initTapes s).
Proof.
destruct s as ((T&V)&Heap).
split.
{
intros (s'&HSteps&HHalt).
apply steps_steps_k in HSteps as (k&HSteps).
destruct (@Loop_Terminates (initTapes (T,V,Heap)) (Loop_steps T V Heap k)) as (outc&Term).
{
cbn.
hnf.
do 4 eexists; repeat split; cbn; eauto.
1: hnf; eauto.
1-3: apply initValue_contains.
intros i; destruct_fin i; cbn; apply initRight_isVoid.
}
hnf.
destruct outc as [q' t'].
exists q', t'.
eapply TM_eval_iff.
eauto.
}
{
intros (tout&k&HLoop).
eapply TM_eval_iff in HLoop as [n HLoop].
pose proof Loop_Realise HLoop as HLoopRel.
hnf in HLoopRel.
modpon HLoopRel.
1-3: apply initValue_contains_size.
instantiate (1 := [| _;_;_;_;_;_;_;_|]).
-
intros i; destruct_fin i; cbn; eapply initRight_isVoid_size.
-
destruct HLoopRel as (T'&V'&H'&k'&HStep&HTerm&_).
cbn in *.
hnf.
eauto.
apply steps_k_steps in HStep.
eauto.
}
