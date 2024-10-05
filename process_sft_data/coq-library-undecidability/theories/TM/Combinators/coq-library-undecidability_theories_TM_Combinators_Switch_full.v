From Undecidability Require Import TM.Util.TM_facts.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.DepPairs EqdepFacts.
Section Switch.
Variable n : nat.
Variable sig : finType.
Variable F : finType.
Variable pM1 : pTM sig F n.
Variable F' : finType.
Variable pMf : F -> pTM sig F' n.
Notation M1 := (projT1 pM1).
Notation p1 := (projT2 pM1).
Notation "'Mf' y" := (projT1 (pMf y)) (at level 10).
Notation "'p2' y" := (projT2 (pMf y)) (at level 10).
Definition Switch_trans : (TM.state M1 + { f : F & TM.state (Mf f) }) * Vector.t (option sig) n -> (TM.state M1 + { f : F & TM.state (Mf f) }) * Vector.t (option sig * move) n := fun '(q, s) => match q with | inl q => if halt q then (inr (existT _ (p1 q) (start (Mf (p1 q)))), nop_action) else let (q', a) := trans (q, s) in (inl q', a) | inr q => let (q', a) := trans (projT2 q, s) in (inr (existT _ (projT1 q) q'), a) end.
Definition Switch_halt : (TM.state M1 + { f : F & TM.state (Mf f) }) -> bool := fun q => match q with | inl _ => false | inr q => halt (projT2 q) end.
Definition SwitchTM : TM sig n := {| trans := Switch_trans; halt := Switch_halt; start := inl (start M1); |}.
Definition Switch_p : (state SwitchTM) -> F' := fun q => match q with | inl q => p2 (p1 q) (start (Mf (p1 q))) (* Canonical value *) | inr q => p2 (projT1 q) (projT2 q) end.
Definition Switch : pTM sig F' n := (SwitchTM; Switch_p).
Definition lift_confL (c : mconfig sig (state M1) n) : mconfig sig (state SwitchTM) n := mk_mconfig (inl (cstate c)) (ctapes c).
Definition lift_confR (f : F) (c : mconfig sig (state (Mf f) ) n) : mconfig sig (state SwitchTM) n := mk_mconfig (inr (existT (fun f0 : F => state (Mf f0)) f (cstate c))) (ctapes c).
Lemma step_comp_liftL (c : mconfig sig (state M1) n) : haltConf c = false -> step (lift_confL c) = lift_confL (step c).
Proof.
unfold lift_confL, step, haltConf.
cbn.
destruct c as [q t]; cbn in *.
intros H.
rewrite H.
destruct (trans _) eqn:E.
cbn.
reflexivity.
Qed.
Lemma step_comp_liftR f (c : mconfig sig (state (Mf f)) n) : step (lift_confR c) = lift_confR (step c).
Proof.
destruct c.
unfold lift_confR, step.
cbn.
destruct (trans _) eqn:E.
cbn.
reflexivity.
Qed.
Definition halt_liftL (c : mconfig sig (state (SwitchTM)) n) := match cstate c with | inl q => halt (m := M1) q | inr q => true end.
Lemma halt_conf_liftL (c : mconfig sig (state SwitchTM) n) : halt_liftL c = false -> halt (cstate c) = false.
Proof.
intros H.
cbn.
unfold Switch_halt.
destruct c as [q t]; cbn.
destruct q; cbn in *; auto.
Qed.
Lemma step_nop_transition (c : mconfig sig (state M1) n) : haltConf c = true -> step (lift_confL c) = lift_confR (initc (Mf (p1 (cstate c))) (ctapes c)).
Proof.
intros Halt.
unfold lift_confL, lift_confR.
cbn.
unfold haltConf in Halt.
unfold step at 1; cbn.
rewrite Halt.
f_equal.
apply doAct_nop.
Qed.
Lemma lift_initc t : initc SwitchTM t = lift_confL (initc M1 t).
Proof.
reflexivity.
Qed.
Lemma Switch_merge t (k1 k2 : nat) (c1 : mconfig sig (state M1) n) (c2 : mconfig sig (state (Mf (p1 (cstate c1)))) n) : loopM (initc M1 t) k1 = Some c1 -> loopM (initc (Mf (p1 (cstate c1))) (ctapes c1)) k2 = Some c2 -> loopM (initc SwitchTM t) (k1 + (1 + k2)) = Some (lift_confR c2).
Proof.
intros HLoop1 HLoop2.
unfold loopM in *.
apply loop_merge with (h := halt_liftL) (a2 := lift_confL c1).
-
apply halt_conf_liftL.
-
rewrite lift_initc.
apply loop_lift with (h := haltConf (M := M1)) (f := step (M := M1)).
+
unfold haltConf.
intros.
cbn.
reflexivity.
+
apply step_comp_liftL.
+
apply HLoop1.
-
rewrite loop_step by auto.
rewrite step_nop_transition by apply (loop_fulfills HLoop1).
eapply loop_lift with (lift := lift_confR (f := p1 (cstate c1))) (f' := step (M := SwitchTM)) (h' := haltConf (M := SwitchTM)) in HLoop2.
+
apply HLoop2.
+
intros.
cbn.
now destruct x.
+
intros.
apply step_comp_liftR.
Qed.
Lemma step_nop_split (k2 : nat) (c2 : mconfig sig (state M1) n) (outc : mconfig sig (state SwitchTM) n) : haltConf c2 = true -> loopM (M := SwitchTM) (lift_confL c2) k2 = Some outc -> exists k2' c2', k2 = S k2' /\ loopM (M := Mf (p1 (cstate c2))) (initc _ (ctapes c2)) k2' = Some c2' /\ outc = lift_confR c2'.
Proof.
unfold loopM.
intros HHalt HLoop2.
unfold haltConf in HHalt.
destruct k2 as [ | k2'].
-
inv HLoop2.
-
exists k2'.
cbn in HLoop2.
rewrite step_nop_transition in HLoop2 by assumption.
apply loop_unlift with (f := step (M := Mf (p1 (cstate c2)))) (h := haltConf (M := Mf (p1 (cstate c2)))) in HLoop2 as (c2'&HLoop2&->).
+
exists c2'.
repeat split.
exact HLoop2.
+
intros.
reflexivity.
+
intros.
apply step_comp_liftR.
Qed.
Lemma Switch_split k t (outc : mconfig sig (state SwitchTM) n) : loopM (initc SwitchTM t) k = Some outc -> exists k1 (c1 : mconfig sig (state M1) n) k2 (c2 : mconfig sig (state (Mf (p1 (cstate c1)))) n), loopM (initc M1 t) k1 = Some c1 /\ loopM (initc (Mf (p1 (cstate c1))) (ctapes c1)) k2 = Some c2 /\ outc = lift_confR c2.
Proof.
unfold loopM.
intros H.
apply loop_split with (h := halt_liftL) in H as (k1&c1&k2&HLoop1&HLoop2&_).
-
rewrite lift_initc in HLoop1.
apply loop_unlift with (lift := lift_confL) (f := step (M := M1)) (h := haltConf (M := M1)) in HLoop1 as (c1'&HLoop1&->).
+
apply step_nop_split in HLoop2 as (k2'&c2'&_&HLoop2&->).
2: now apply (loop_fulfills HLoop1).
exists k1, c1', k2', c2'.
auto.
+
intros.
cbn.
reflexivity.
+
intros.
now apply step_comp_liftL.
-
apply halt_conf_liftL.
Qed.
Lemma Switch_Realise (R1 : Rel _ (F * _)) (R2 : F -> Rel _ (F' * _)) : pM1 ⊨ R1 -> (forall f : F, pMf f ⊨ R2 f) -> Switch ⊨ (⋃_f (R1 |_ f) ∘ R2 f).
Proof.
intros HRel1 HRel2.
hnf in HRel1.
hnf.
intros t i outc HLoop.
apply Switch_split in HLoop as (k1&c1&k2&c2&HLoop1&HLoop2&->).
cbn.
exists (p1 (cstate c1)), (ctapes c1).
split.
-
apply (HRel1 _ _ _ HLoop1).
-
apply (HRel2 _ _ _ _ HLoop2).
Qed.
Lemma Switch_TerminatesIn (R1 : Rel _ (F * _)) T1 T2 : pM1 ⊨ R1 -> M1 ↓ T1 -> (forall f : F, Mf f ↓(T2 f)) -> projT1 Switch ↓ (fun tin i => exists i1 i2, T1 tin i1 /\ 1 + i1 + i2 <= i /\ forall tout yout, R1 tin (yout, tout) -> T2 yout tout i2).
Proof.
unfold Switch.
intros HRel1 HTerm1 HTerm2.
hnf in HRel1, HTerm1.
hnf.
intros t i (i1&i2&HT1&Hk&H).
specialize HTerm1 with (1 := HT1) as (c1&HLoop1).
specialize HRel1 with (1 := HLoop1).
specialize H with (1 := HRel1).
specialize (HTerm2 _ _ _ H) as (c2&HLoop2).
pose proof Switch_merge HLoop1 HLoop2 as HLoop.
exists (lift_confR c2).
eapply loop_monotone; eauto.
lia.
Qed.
Lemma Switch_TerminatesIn' (R1 : Rel _ (F * _)) T1 T2 : pM1 ⊨ R1 -> M1 ↓ T1 -> (forall f : F, Mf f ↓(T2 f)) -> projT1 Switch ↓ (fun tin i => exists i1, T1 tin i1 /\ forall tout yout, R1 tin (yout, tout) -> exists i2, 1 + i1 + i2 <= i /\ T2 yout tout i2).
Proof.
unfold Switch.
intros HRel1 HTerm1 HTerm2.
hnf in HRel1, HTerm1.
hnf.
intros t k (i1&HT1&H).
specialize HTerm1 with (1 := HT1) as (c1&HLoop1).
specialize HRel1 with (1 := HLoop1).
specialize H with (1 := HRel1) as (i2&Hi&HT2).
unfold TerminatesIn in HTerm2.
specialize HTerm2 with (1 := HT2) as (c2&HLoop2).
pose proof Switch_merge HLoop1 HLoop2 as HLoop.
exists (lift_confR c2).
eapply loop_monotone; eauto.
lia.
Qed.
Lemma Switch_RealiseIn (R1 : Rel _ (F * _)) (R2 : F -> Rel _ (F' * _)) k1 k2: pM1 ⊨c(k1) R1 -> (forall f : F, pMf f ⊨c(k2) R2 f) -> Switch ⊨c(1 + k1 + k2) (⋃_f (R1 |_ f) ∘ R2 f).
Proof.
intros (H1&H2) % Realise_total H3.
apply Realise_total.
split.
-
eapply Switch_Realise; eauto.
intros ?.
eapply Realise_total; eauto.
-
eapply TerminatesIn_monotone.
+
apply Switch_TerminatesIn; eauto.
intros ?.
eapply Realise_total; eauto.
+
firstorder.
Qed.
End Switch.
Arguments Switch : simpl never.
Notation MATCH := Switch (only parsing).
Notation Match := Switch (only parsing).