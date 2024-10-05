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

Lemma StateWhile_split k l (c1 : mconfig sig (state (projT1 (pM l))) n) (c3 : mconfig sig (FinType (EqType StateWhile_states)) n) : loopM (StateWhileTM l) (lift c1) k = Some c3 -> exists (c2 : mconfig sig (state (projT1 (pM l))) n), match projT2 (pM l) (cstate c2) with | inl l1 => exists (k1 k2 : nat), loopM (projT1 (pM l)) c1 k1 = Some c2 /\ loopM (StateWhileTM l) (lift (initc (projT1 (pM l1)) (ctapes c2))) k2 = Some c3 /\ 1 + k1 + k2 <= k | inr l2 => loopM (projT1 (pM l)) c1 k = Some c2 /\ c3 = lift c2 end.
Proof.
intros HLoop.
unfold loopM in *.
apply loop_split with (h := @lifth l) in HLoop as (k1&c2&k2&HLoop1&HLoop2&Hk).
-
apply loop_unlift with (f := step (projT1 (pM l))) (h := haltConf (M := projT1 (pM l))) in HLoop1 as (c2'&HLoop1&->).
+
exists c2'.
destruct (projT2 (pM l) (cstate c2')) as [l1|l2] eqn:E.
*
exists k1.
eapply StateWhile_split_repeat in HLoop2 as (k2'&HLoop2&->).
exists k2'.
repeat split.
all: eauto.
--
lia.
--
now apply loop_fulfills in HLoop1.
*
split.
eapply loop_monotone.
apply HLoop1.
lia.
eapply StateWhile_split_break; eauto.
now apply loop_fulfills in HLoop1.
+
apply lifth_comp'.
+
apply step_comp.
-
apply lifth_comp.
