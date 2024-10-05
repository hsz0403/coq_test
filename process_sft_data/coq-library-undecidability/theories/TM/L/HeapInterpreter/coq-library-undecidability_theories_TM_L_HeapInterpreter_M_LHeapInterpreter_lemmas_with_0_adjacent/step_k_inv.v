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

Lemma step_k_inv T V H T2 V2 H2 k : steps_k k (T, V, H) (T2, V2, H2) -> (k=0/\T=T2/\V=V2/\H=H2) \/ (exists T1 V1 H1 k', k=S k' /\ step (T,V,H) (T1,V1,H1) /\ steps_k k' (T1,V1,H1) (T2,V2,H2)).
Proof.
intros.
destruct k.
-
inv H0.
now left.
-
eapply pow_add with (n:=1) in H0.
destruct H0 as (((?&?)&?)&?%rcomp_1&?).
right.
do 4 eexists.
repeat split; eauto.
