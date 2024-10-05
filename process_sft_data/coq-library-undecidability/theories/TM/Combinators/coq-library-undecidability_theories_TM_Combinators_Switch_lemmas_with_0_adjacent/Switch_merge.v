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
Definition halt_liftL (c : mconfig sig (state (SwitchTM)) n) := match cstate c with | inl q => halt (m := M1) q | inr q => true end.
End Switch.
Arguments Switch : simpl never.
Notation MATCH := Switch (only parsing).
Notation Match := Switch (only parsing).

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
