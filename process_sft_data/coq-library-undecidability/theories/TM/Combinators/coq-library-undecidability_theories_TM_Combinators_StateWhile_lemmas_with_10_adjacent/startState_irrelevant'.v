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

Lemma step_comp (l : F1) (c : mconfig sig (state (projT1 (pM l))) n) : haltConf c = false -> step (StateWhileTM l) (lift c) = lift (step (projT1 (pM l)) c).
Proof.
intros HHalt.
unfold haltConf in HHalt.
unfold lift.
destruct c as [q t].
cbn in *.
cbv [step].
cbn.
rewrite HHalt.
destruct (trans (q, current_chars t)) as [q' a].
cbn.
Admitted.

Lemma halt_comp (l : F1) (c : mconfig sig (state (projT1 (pM l))) n) : haltConf (M := projT1 (pM l)) c = false -> haltConf (M := StateWhileTM l) (lift c) = false.
Proof.
intros HHalt.
cbn in *.
destruct c as [q t].
cbn in *.
apply andb_false_iff.
cbn.
Admitted.

Lemma halt_comp' (l : F1) (c : mconfig sig (state (projT1 (pM l))) n) : haltConf (M := StateWhileTM l) (lift c) = haltConf (M := projT1 (pM l)) c.
Proof.
cbn in *.
destruct c as [q t].
cbn in *.
unfold StateWhile_halt, haltConf.
Admitted.

Lemma StateWhile_trans_repeat (l l_ : F1) (c : mconfig sig (state (projT1 (pM l))) n) (l' : F1) : haltConf (M := projT1 (pM l)) c = true -> projT2 (pM l) (cstate c) = inl l' -> step (StateWhileTM l_) (lift c) = lift (initc (projT1 (pM l')) (ctapes c)).
Proof.
intros HHalt HRepeat.
unfold haltConf in HHalt.
destruct c as [q t]; cbn in *.
unfold step.
cbn -[doAct_multi] in *.
rewrite HHalt, HRepeat.
unfold initc, lift.
cbn.
f_equal.
Admitted.

Lemma startState_irrelevant k l l' c1 c2 : loopM (StateWhileTM l ) c1 k = Some c2 -> loopM (StateWhileTM l') c1 k = Some c2.
Proof.
Admitted.

Definition lifth l : mconfig sig (state (StateWhileTM l)) n -> bool.
Proof.
intros ((l'&q)&t).
decide (l=l') as [_ | ].
-
eapply (halt _ q).
-
Admitted.

Lemma lifth_comp l (c : mconfig sig (state (StateWhileTM l)) n) : lifth c = false -> haltConf c = false.
Proof.
destruct c as ((l'&q)&t).
cbn.
decide (l=l') as [->| _]; intros H; auto.
unfold StateWhile_halt.
cbn.
Admitted.

Lemma lifth_comp' l (c : mconfig sig (state (projT1 (pM l))) n) : @lifth l (lift c) = haltConf c.
Proof.
unfold haltConf.
destruct c as (q,t).
cbn.
Admitted.

Lemma StateWhile_split_repeat k l l1 c2 c3 : loop (step (StateWhileTM l)) (haltConf (M:=StateWhileTM l)) (lift c2) k = Some c3 -> haltConf c2 = true -> projT2 (pM l) (cstate c2) = inl l1 -> exists k', loop (step (StateWhileTM l)) (haltConf (M:=StateWhileTM l)) (lift (initc (projT1 (pM l1)) (ctapes c2))) k' = Some c3 /\ k = S k'.
Proof.
intros HLoop H E.
unfold haltConf in H.
destruct k as [ |k']; cbn in *; unfold StateWhile_halt in *; cbn in *.
-
rewrite H, E in HLoop.
cbn in *.
congruence.
-
rewrite H, E in HLoop.
cbn in *.
exists k'.
repeat split; auto.
rewrite <- HLoop.
f_equal.
symmetry.
Admitted.

Lemma StateWhile_split_break k l l2 c2 c3 : loop (step (StateWhileTM l)) (haltConf (M:=StateWhileTM l)) (lift c2) k = Some c3 -> haltConf c2 = true -> projT2 (pM l) (cstate c2) = inr l2 -> c3 = lift c2.
Proof.
intros HLoop H E.
eapply loop_eq_0 in HLoop; auto.
unfold haltConf in *.
cbn in *.
unfold StateWhile_halt in *.
cbn in *.
Admitted.

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
Admitted.

Lemma StateWhile_merge_repeat k1 k2 l l1 (c1 : mconfig sig (state (projT1 (pM l))) n) (c2 : mconfig sig (state (projT1 (pM l))) n) c3 : loopM (projT1 (pM l)) c1 k1 = Some c2 -> haltConf c2 = true -> projT2 (pM l) (cstate c2) = inl l1 -> loopM (StateWhileTM l) (lift (initc (projT1 (pM l1)) (ctapes c2))) k2 = Some c3 -> loopM (StateWhileTM l) (lift c1) (k1 + (1 + k2)) = Some c3.
Proof.
intros HLoop1 HHalt HL HLoop2.
unfold loopM in *.
apply loop_merge with (f := step (StateWhileTM l)) (h := @lifth l) (a2 := lift c2).
-
apply lifth_comp.
-
eapply loop_lift.
3: apply HLoop1.
2: eauto.
+
apply lifth_comp'.
+
apply step_comp.
-
cbn [plus].
rewrite loop_step.
+
now rewrite StateWhile_trans_repeat with (l' := l1).
+
cbn; unfold StateWhile_halt; cbn.
rewrite HL.
Admitted.

Lemma StateWhile_merge_break k l l2 (c1 : mconfig sig (state (projT1 (pM l))) n) (c2 : mconfig sig (state (projT1 (pM l))) n) : loopM (projT1 (pM l)) c1 k = Some c2 -> haltConf c2 = true -> projT2 (pM l) (cstate c2) = inr l2 -> loopM (StateWhileTM l) (lift c1) k = Some (lift c2).
Proof.
intros HLoop HHalt HL.
unfold loopM in *.
replace k with (k + 0) by lia.
apply loop_merge with (f := step (StateWhileTM l)) (h := @lifth l) (a2 := lift c2).
-
apply lifth_comp.
-
eapply loop_lift with (lift := lift) (f' := step (StateWhileTM l)) (h' := @lifth l) in HLoop; auto.
+
apply lifth_comp'.
+
apply step_comp.
-
cbn.
unfold StateWhile_halt; cbn.
unfold haltConf in *.
rewrite HHalt, HL.
cbn.
Admitted.

Lemma lift_init l tin : initc (StateWhileTM l) tin = lift (initc (projT1 (pM l)) tin).
Proof.
Admitted.

Lemma StateWhile_Realise l : (forall l, pM l ⊨ R l) -> StateWhile l ⊨ StateWhile_Rel l.
Proof.
intros HRel.
hnf in HRel; hnf.
intros t k; revert t l.
apply complete_induction with (x := k); clear k; intros k IH.
intros tin l c3 HLoop.
unfold loopM in HLoop.
cbn in *.
rewrite lift_init in HLoop.
apply StateWhile_split in HLoop as (c2&HLoop).
destruct (projT2 (pM l) (cstate c2)) as [l1|l2] eqn:E.
-
destruct HLoop as (k1&k2&HLoop1&HLoop2&Hk).
apply HRel in HLoop1.
rewrite E in HLoop1.
rewrite <- lift_init in HLoop2.
eapply startState_irrelevant in HLoop2.
specialize IH with (2 := HLoop2).
spec_assert IH by lia.
econstructor 1; eauto.
-
destruct HLoop as (HLoop&->).
apply HRel in HLoop.
rewrite E in *.
constructor 2; auto.
cbn.
unfold StateWhile_part.
cbn.
Admitted.

Lemma startState_irrelevant' k l l' c1 : loopM (StateWhileTM l) c1 k = loopM (StateWhileTM l') c1 k.
Proof.
reflexivity.
