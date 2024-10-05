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
