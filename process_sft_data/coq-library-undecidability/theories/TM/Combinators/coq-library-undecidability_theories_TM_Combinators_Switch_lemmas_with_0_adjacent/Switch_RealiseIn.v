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
