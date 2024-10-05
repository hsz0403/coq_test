From Undecidability Require Import TM.Util.TM_facts.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.DepPairs EqdepFacts.
Section While.
Variable n : nat.
Variable sig : finType.
Variable F : finType.
Variable pM : pTM sig (option F) n.
Definition While_trans : (TM.state (projT1 pM)) * Vector.t (option sig) n -> (TM.state (projT1 pM)) * Vector.t (option sig * move) n := fun '(q,s) => if halt q then (start (projT1 pM), nop_action) else trans (q,s).
Definition WhileTM : TM sig n := Build_TM While_trans (start (projT1 pM)) (fun q => halt q && match projT2 pM q with | Some _ => true | None => false end).
Hypothesis (defF : inhabitedC F).
Definition While_part : state (projT1 pM) -> F := fun q => match projT2 pM q with | Some y => y | None => default end.
Definition While : pTM sig F n := (WhileTM; While_part).
Local Arguments loopM {_ _} _ _ _.
Local Arguments halt {_ _} _ _.
Local Arguments step {_ _} _ _.
Variable R : pRel sig (option F) n.
Inductive While_Rel : pRel sig F n := | While_Rel''_one : forall tin yout tout, R tin (Some yout, tout) -> While_Rel tin (yout, tout) | While_Rel''_loop : forall tin tmid yout tout, R tin (None, tmid) -> While_Rel tmid (yout, tout) -> While_Rel tin (yout, tout).
Section While_TerminatesIn.
Variable (T T' : Rel (tapes sig n) nat).
End While_TerminatesIn.
Section While_TerminatesIn_coind.
Variable (T : Rel (tapes sig n) nat).
CoInductive While_T : tRel sig n := | While_T_intro tin k k1 : T tin k1 -> (forall tmid ymid, R tin (Some ymid, tmid) -> k1 <= k) -> (forall tmid, R tin (None, tmid) -> exists k2, While_T tmid k2 /\ 1 + k1 + k2 <= k) -> While_T tin k.
End While_TerminatesIn_coind.
End While.
Arguments While : simpl never.
Arguments While {n sig F} pM {defF}.
Notation WHILE := While (only parsing).
Section WhileInduction.
Variable (sig : finType) (n : nat) (F : finType).
Variable R1 : pRel sig (option F) n.
Variable R2 : pRel sig F n.
End WhileInduction.
Section WhileCoInduction.
Variable (sig : finType) (n : nat) (F : finType).
Variable R : pRel sig (option F) n.
Variable T T' : tRel sig n.
End WhileCoInduction.
Section OtherWhileRel.
Variable (sig : finType) (n : nat) (F : finType).
Variable R : Rel (tapes sig n) (option F * tapes sig n).
Definition While_Rel' : pRel sig F n := (star (R |_ None)) ∘ ⋃_y (R |_(Some y)) ||_y.
Goal While_Rel R =2 While_Rel'.
Proof.
unfold While_Rel'.
split.
{
apply WhileInduction; intros; cbn in *.
-
eexists.
split.
constructor.
exists yout.
auto.
-
destruct HLastStep as (y&IH1&?&<-&IH2); cbn in *.
eexists.
split; eauto.
econstructor; eauto.
}
{
intros tin (yout, tout) H.
cbn in H.
destruct H as (tmid&HStar&HLastStep).
induction HStar as [ tin | tin tmid tmid2 HS1 HS2 IH].
-
destruct HLastStep as (?&<-&H).
now constructor.
-
spec_assert IH by assumption.
destruct HLastStep as (?&<-&H).
econstructor 2.
+
apply HS1.
+
apply IH.
}
End OtherWhileRel.

Lemma While_TerminatesIn : pM ⊨ R -> projT1 pM ↓ T -> WhileTM ↓ While_T.
Proof.
intros HRel HTerm.
eapply While_TerminatesIn_ind; eauto.
intros tin k' HCoInd.
destruct HCoInd as [ t k k1 H1 H2 H3 ].
eauto.
