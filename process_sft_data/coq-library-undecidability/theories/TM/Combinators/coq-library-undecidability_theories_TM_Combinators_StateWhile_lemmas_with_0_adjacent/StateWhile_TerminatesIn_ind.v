From Undecidability Require Export TM.Util.TM_facts.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.DepPairs EqdepFacts.
Section StateWhile.
Variable n : nat.
Variable sig : finType.
Variable F1 F2 : finType.
Variable pM : F1 -> pTM sig (F1 + F2) n.
Definition StateWhile_states : Type := { l : F1 & state (projT1 (pM l)) }.
Definition liftState {l : F1} (q : state (projT1 (pM l))) : StateWhile_states := ltac:(eexists; apply q).
Definition lift {l : F1} (c : mconfig sig (state (projT1 (pM l))) n) : mconfig sig (FinType(EqType StateWhile_states)) n := {| cstate := liftState (cstate c); ctapes := ctapes c; |}.
Definition StateWhile_trans : StateWhile_states * Vector.t (option sig) n -> StateWhile_states * Vector.t (option sig * move) n := fun '(q, s) => if halt (projT2 q) then match projT2 (pM (projT1 q)) (projT2 q) with | inl l1 => (liftState (start (projT1 (pM l1))), nop_action) | inr _ => (q, nop_action) (* terminating state, transition is irrelevant *) end else let (q', a) := trans (projT2 q, s) in (liftState q', a).
Definition StateWhile_halt : StateWhile_states -> bool := fun q => halt (projT2 q) && match projT2 (pM (projT1 q)) (projT2 q) with | inl _ => false | inr l2 => true end.
Definition StateWhileTM (l1 : F1) : TM sig n := {| start := liftState (start (projT1 (pM l1))); trans := StateWhile_trans; halt := StateWhile_halt; |}.
Hypothesis (defF : inhabitedC F2).
Definition StateWhile_part : StateWhile_states -> F2 := fun q => match projT2 (pM (projT1 q)) (projT2 q) with | inl _ => default | inr l2 => l2 end.
Definition StateWhile (l1 : F1) : pTM sig F2 n := (StateWhileTM l1; StateWhile_part).
Local Arguments loopM {_ _} _ _ _.
Local Arguments halt {_ _} _ _.
Local Arguments step {_ _} _ _.
Definition lifth l : mconfig sig (state (StateWhileTM l)) n -> bool.
Proof.
intros ((l'&q)&t).
decide (l=l') as [_ | ].
-
eapply (halt _ q).
-
apply true.
Defined.
Variable R : F1 -> pRel sig (F1 + F2) n.
Inductive StateWhile_Rel : F1 -> pRel sig F2 n := | StateWhile_Rel_loop : forall l t l1 t' l' t'', R l t (inl l1, t') -> StateWhile_Rel l1 t' (l', t'') -> StateWhile_Rel l t (l', t'') | StateWhile_Rel_break : forall l t l2 t', R l t (inr l2, t') -> StateWhile_Rel l t (l2, t').
Section StateWhile_TerminatesIn.
Variable (T T' : F1 -> tRel sig n).
End StateWhile_TerminatesIn.
Section StateWhile_TerminatesIn_coind.
Variable (T : F1 -> tRel sig n).
CoInductive StateWhile_T : F1 -> tRel sig n := | StateWhile_T_intro l t k k1 : T l t k1 -> (forall t' l1, R l t (inl l1, t') -> exists k2, StateWhile_T l1 t' k2 /\ 1 + k1 + k2 <= k) -> (forall tmid l2, R l t (inr l2, tmid) -> k1 <= k) -> StateWhile_T l t k.
End StateWhile_TerminatesIn_coind.
End StateWhile.
Arguments StateWhile : simpl never.
Arguments StateWhile {n sig F1 F2} pM {defF} l1.
Section StateWhileInduction.
Variable (sig : finType) (n : nat) (F1 F2 : finType).
Variable R1 : F1 -> pRel sig (F1+F2) n.
Variable R2 : F1 -> pRel sig F2 n.
End StateWhileInduction.
Section WhileCoInduction.
Variable (sig : finType) (n : nat) (F1 F2 : finType).
Variable R : F1 -> pRel sig (F1 + F2) n.
Variable T T' : F1 -> tRel sig n.
End WhileCoInduction.

Lemma StateWhile_TerminatesIn_ind l : (forall l, pM l ⊨ R l) -> (forall l, projT1 (pM l) ↓ T' l) -> (forall l (tin : tapes sig n) (k : nat), T l tin k -> exists k1, T' l tin k1 /\ (forall tmid l2, R l tin (inr l2, tmid) -> k1 <= k) /\ (forall tmid l1, R l tin (inl l1, tmid) -> exists k2, T l1 tmid k2 /\ 1 + k1 + k2 <= k)) -> StateWhileTM l ↓ T l.
Proof.
intros Realise_M Term_M Hyp tin k.
revert tin l.
apply complete_induction with (x:=k); clear k; intros k IH tin l.
intros (k1&HT1&HT2&HT3) % Hyp.
pose proof (Term_M _ _ _ HT1) as (oconf&Hloop).
specialize (Realise_M _ _ _ _ Hloop).
destruct (projT2 (pM l) (cstate oconf)) as [ l1 | l2 ] eqn:E1.
-
specialize HT3 with (1 := Realise_M) as (k2&HT3&Hi).
specialize (IH k2 ltac:(lia) _ _ HT3) as (oconf2&Hloop2).
exists oconf2.
apply loop_monotone with (k1 := k1 + (1 + k2)).
2: lia.
cbn -[plus].
rewrite lift_init.
refine (StateWhile_merge_repeat Hloop _ _ Hloop2); auto.
unfold loopM in *; now apply loop_fulfills in Hloop.
-
specialize HT2 with (1 := Realise_M).
exists (lift oconf).
eapply loop_monotone; eauto.
refine (StateWhile_merge_break (l2 := l2) Hloop _ _); auto.
unfold loopM in *; now apply loop_fulfills in Hloop.
