From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

Lemma If_SpecTReg (sig : finType) (n : nat) (F : finType) (pM1 : pTM _ bool n) (pM2 pM3 : pTM _ F n) (P : Spec sig n) (Q : bool -> Spec sig n) (R : F -> Spec sig n) (k k1 k2 k3 : nat) : TripleT ≃≃( P) k1 pM1 (fun y => ≃≃( Q y)) -> TripleT ≃≃( Q true) k2 pM2 (fun y => ≃≃( R y)) -> TripleT ≃≃( Q false) k3 pM3 (fun y => ≃≃( R y)) -> (implList (fst P) (forall b, implList (fst (Q b)) (1 + k1 + (if b then k2 else k3) <= k))) -> TripleT ≃≃( P) k (If pM1 pM2 pM3) (fun y => ≃≃( R y)).
Proof.
intros H1 H2 H3 H4.
eapply If_SpecT.
1-3:eassumption.
cbn.
intros.
do 2 setoid_rewrite implList_iff in H4.
specialize H4 with (b:=yout).
destruct P,(Q yout).
eapply H4;cbn.
Admitted.

Lemma If_SpecT_weak (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n) (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n) (k k1 k2 k3 : nat) : TripleT P k1 pM1 Q -> TripleT (Q true) k2 pM2 R -> TripleT (Q false) k3 pM3 R -> (1 + k1 + max k2 k3 <= k) -> TripleT P k (If pM1 pM2 pM3) R.
Proof.
intros.
eapply If_SpecT; eauto.
intros.
destruct yout.
+
assert (k2 <= max k2 k3) by apply Nat.le_max_l.
lia.
+
assert (k3 <= max k2 k3) by apply Nat.le_max_r.
Admitted.

Lemma If_SpecT_weak' (sig : finType) (n : nat) (F : finType) (pM1 : pTM sig bool n) (pM2 pM3 : pTM sig F n) (P : Assert sig n) (Q : bool -> Assert sig n) (R : F -> Assert sig n) (k k1 k2 : nat) : TripleT P k1 pM1 Q -> TripleT (Q true) k2 pM2 R -> TripleT (Q false) k2 pM3 R -> (1 + k1 + k2 <= k) -> TripleT P k (If pM1 pM2 pM3) R.
Proof.
intros H1 H2 H3 H4.
eapply ConsequenceT_pre.
-
eapply If_SpecT_weak with (k2 := k2) (k3 := k2); eauto.
-
auto.
-
Admitted.

Lemma Switch_Spec (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : F1 -> pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) : Triple P pM1 Q -> (forall (y : F1), Triple (Q y) (pM2 y) R) -> Triple P (Switch pM1 pM2) R.
Proof.
intros H1 H2.
eapply TripleI, Realise_monotone.
-
apply Switch_Realise.
+
apply H1.
+
apply H2.
-
intros tin (yout, tout) H.
cbn in *.
Admitted.

Lemma Switch_SpecT (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : F1 -> pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) (k k1 k2 : nat) : TripleT P k1 pM1 Q -> (forall (y : F1), TripleT (Q y) k2 (pM2 y) R) -> (1 + k1 + k2 <= k) -> TripleT P k (Switch pM1 pM2) R.
Proof.
intros H1 H2 H3.
split.
-
eapply Switch_Spec.
+
apply H1.
+
apply H2.
-
eapply TerminatesIn_monotone.
+
apply Switch_TerminatesIn.
*
apply H1.
*
apply H1.
*
apply H2.
+
unfold Triple_TRel.
intros tin k' (H&Hk).
exists k1, k2.
repeat split; eauto.
Admitted.

Lemma Switch_SpecT_strong (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM sig F1 n) (pM2 : F1 -> pTM sig F2 n) (P : Assert sig n) (Q : F1 -> Assert sig n) (R : F2 -> Assert sig n) (k k1 : nat) (k2 : F1 -> nat) : TripleT P k1 pM1 Q -> (forall (y : F1), TripleT (Q y) (k2 y) (pM2 y) R) -> (forall tin yout tout, P tin -> Q yout tout -> 1 + k1 + k2 yout <= k) -> TripleT P k (Switch pM1 pM2) R.
Proof.
intros H1 H2 H3.
split.
-
eapply Switch_Spec.
+
apply H1.
+
apply H2.
-
eapply TerminatesIn_monotone.
+
apply Switch_TerminatesIn'.
*
apply H1.
*
apply H1.
*
apply H2.
+
unfold Triple_TRel.
intros tin k' (H&Hk).
exists k1.
repeat split.
*
assumption.
*
reflexivity.
*
unfold Triple_Rel.
intros tmid ymid Hmid.
modpon Hmid.
specialize H3 with (1 := H) (2 := Hmid).
exists (k2 ymid).
repeat split; eauto.
Admitted.

Lemma Switch_SpecTReg (sig : finType) (n : nat) (F1 F2 : finType) (pM1 : pTM _ F1 n) (pM2 : F1 -> pTM _ F2 n) (P : Spec sig n) Q R (k k1 : nat) (f : F1 -> nat) : TripleT ≃≃(P) k pM1 (fun y => ≃≃(Q y)) -> (forall (y : F1), TripleT ≃≃(Q y) (f y) (pM2 y) (fun y => ≃≃(R y))) -> (implList (fst P) (forall y, implList (fst (Q y)) (1 + k + f y <= k1))) -> TripleT ≃≃(P) k1 (Switch pM1 pM2) (fun y => ≃≃(R y)).
Proof.
intros H1 H2 H3.
eapply Switch_SpecT_strong.
1-2:eassumption.
intros.
destruct P.
eapply tspecE in H as [].
eapply implListE in H3.
2:easy.
setoid_rewrite implList_iff in H3.
apply H3.
cbn in H0.
destruct Q.
Admitted.

Lemma While_Spec0 (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM sig (option F) n) (P : Assert sig n) (Q : option F -> Assert sig n) (R : F -> Assert sig n) : Triple P pM Q -> (forall yout tout, Q (Some yout) tout -> R yout tout) -> (forall tmid, Q None tmid -> P tmid) -> Triple P (While pM) R.
Proof.
intros H1 H3 H2.
eapply TripleI, Realise_monotone.
{
TM_Correct.
apply H1.
}
{
clear H1.
unfold Triple_Rel in *.
apply WhileInduction; firstorder.
Admitted.

Lemma While_Spec (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM sig (option F) n) (X : Type) (P : X -> Assert sig n) (Q : X -> option F -> Assert sig n) (R : X -> F -> Assert sig n) : (forall x, Triple (P x) pM (Q x)) -> (forall x yout tmid tout, P x tmid -> Q x (Some yout) tout -> R x yout tout) -> (forall x tin tmid, P x tin -> Q x None tmid -> exists x', P x' tmid /\ forall yout tout, R x' yout tout -> R x yout tout) -> forall (x : X), Triple (P x) (While pM) (R x).
Proof.
intros H1 H2 H3.
enough (While pM ⊨ fun tin '(yout, tout) => forall (x : X), P x tin -> R x yout tout) as H.
{
clear H1 H2 H3.
intros.
rewrite Triple_iff.
unfold Triple_Rel, Realise in *.
eauto.
}
{
eapply Realise_monotone.
{
clear H2 H3.
apply While_Realise with (R := fun tin '(yout, tout) => forall (x : X), P x tin -> Q x yout tout).
hnf.
setoid_rewrite Triple_iff in H1.
unfold Triple_Rel in *.
firstorder.
}
{
clear H1.
apply WhileInduction; intros.
-
eapply H2; eauto.
-
specialize HStar with (1 := H).
specialize H3 with (1 := H) (2 := HStar) as (x'&H3&H3').
eapply H3'; eauto.
}
Admitted.

Lemma While_SpecReg (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM _ (option F) n) (X : Type) (P : X -> Spec sig n) (Q : X -> option F -> Spec sig n) (R : X -> F -> Spec sig n) : (forall x, Triple ≃≃( P x) pM (fun y => ≃≃( Q x y))) -> (forall x , implList (fst (P x)) (forall yout, implList (fst (Q x (Some yout))) (Entails ≃≃( [],snd (Q x (Some yout))) ≃≃( R x yout))) /\ (implList (fst (Q x None)) (exists x', Entails ≃≃( [],snd (Q x None)) ≃≃( P x') /\ (forall yout, Entails ≃≃( R x' yout) ≃≃( R x yout))))) -> forall (x : X), Triple ≃≃( P x) (While pM) (fun y => ≃≃( R x y)).
Proof.
intros H1 H2.
eapply While_Spec with (1:=H1).
-
intros ? ? ? ? ?.
revert tout.
apply EntailsE.
specialize (H2 x) as [H2 ?].
destruct (P x);cbn in *.
apply tspecE in H as [H _].
do 2 setoid_rewrite implList_iff in H2.
specialize (H2 H yout).
destruct (Q x (Some yout));cbn in *.
eapply tspec_introPure.
rewrite implList_iff.
eauto.
-
intros **.
specialize (H2 x) as [? H2].
destruct (P x);cbn in *.
apply tspecE in H as [H _].
setoid_rewrite implList_iff in H2.
destruct (Q x None);cbn in *.
eapply tspecE in H0 as (H0&?).
specialize (H2 H0) as (x'&H2&H').
eexists x'.
split.
{
eapply (EntailsE H2).
eapply tspecI.
now hnf.
easy.
}
intros ? .
Admitted.

Lemma While_SpecTReg (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM _ (option F) n) (X : Type) (f__loop f__step : X -> nat) (PRE : X -> Spec sig n) (INV : X -> option F -> Spec sig n) (POST : X -> F -> Spec sig n) : (forall x, TripleT ≃≃( PRE x) (f__step x) pM (fun y => ≃≃( INV x y))) -> (forall x , implList (fst (PRE x)) (forall yout, implList (fst (INV x (Some yout))) (Entails ≃≃( [],snd (INV x (Some yout))) ≃≃( POST x yout) /\ f__step x <= f__loop x)) /\ (implList (fst (INV x None)) (exists x', Entails ≃≃( [],snd (INV x None)) ≃≃( PRE x') /\ 1 + f__step x + f__loop x' <= f__loop x /\ (forall yout, Entails ≃≃( POST x' yout) ≃≃( POST x yout))))) -> forall (x : X), TripleT ≃≃( PRE x) (f__loop x) (While pM) (fun y => ≃≃( POST x y)).
Proof.
intros H1 H2.
eapply While_SpecT with (1:=H1).
-
intros x y ? ? ? H'.
specialize (H2 x) as [H2 ?].
setoid_rewrite implList_iff in H2.
destruct (PRE _).
apply tspecE in H as [H _].
specialize (H2 H y).
destruct (POST x y).
destruct (INV x (Some _)).
specialize (tspecE H') as [H'1 ?].
setoid_rewrite implList_iff in H2.
specialize (H2 H'1) as [].
split.
2:easy.
eapply H2.
eapply tspecI.
all:easy.
-
intros **.
specialize (H2 x) as [? H2].
destruct (PRE _).
destruct (INV _ _).
apply tspecE in H as [H _].
setoid_rewrite implList_iff in H2.
eapply tspecE in H0 as (H0&?).
specialize (H2 H0) as (x'&H2&?&H').
eexists x'.
split.
{
eapply (EntailsE H2).
eapply tspecI.
now hnf.
easy.
}
split.
easy.
intros ? .
Admitted.

Lemma While_SpecTReg' (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM _ (option F) n) (X : Type) (f g : X -> nat) P' Q' R' (P : X -> SpecV sig n) (Q : X -> option F -> SpecV sig n) (R : X -> F -> SpecV sig n) : (forall x, TripleT ≃≃( P' x, P x) (g x) pM (fun y => ≃≃( Q' x y, Q x y))) -> (forall x , implList (P' x) (forall yout, implList (Q' x (Some yout)) (Entails ≃≃( [],Q x (Some yout)) ≃≃( R' x yout,R x yout) /\ g x <= f x)) /\ (implList (Q' x None) (exists x', Entails ≃≃( [],Q x None) ≃≃( P' x', P x') /\ 1 + g x + f x' <= f x /\ (forall yout, Entails ≃≃( R' x' yout,R x' yout) ≃≃( R' x yout,R x yout))))) -> forall (x : X), TripleT ≃≃( P' x,P x) (f x) (While pM) (fun y => ≃≃( R' x y,R x y)).
Proof.
intros H1 H2.
eapply While_SpecTReg with (INV := fun _ _ => (_,_)).
Admitted.

Lemma While_SpecT (sig : finType) (n : nat) (F : finType) {inF : inhabitedC F} (pM : pTM sig (option F) n) (X : Type) (f g : X -> nat) (P : X -> Assert sig n) (Q : X -> option F -> Assert sig n) (R : X -> F -> Assert sig n) : (forall x, TripleT (P x) (g x) pM (Q x)) -> (forall x yout tmid tout, P x tmid -> Q x (Some yout) tout -> R x yout tout /\ g x <= f x) -> (forall x tin tmid, P x tin -> Q x None tmid -> exists x', P x' tmid /\ 1 + g x + f x' <= f x /\ forall yout tout, R x' yout tout -> R x yout tout) -> forall (x : X), TripleT (P x) (f x) (While pM) (R x).
Proof.
intros H1 H2 H3 x.
split.
{
eapply While_Spec; eauto.
-
intros y yout tmid tout Hp Hq.
specialize H2 with (1 := Hp) (2 := Hq).
firstorder.
-
intros x' tin tmid Hp Hq.
specialize H3 with (1 := Hp) (2 := Hq).
firstorder.
}
enough (projT1 (While pM) ↓ (fun tin k => exists x, P x tin /\ f x <= k)) as H.
{
clear H1 H2 H3.
unfold Triple_TRel, TerminatesIn.
firstorder.
}
{
clear x.
eapply TerminatesIn_monotone.
{
clear H2 H3.
apply While_TerminatesIn with (R := fun tin '(yout, tout) => forall (x : X), P x tin -> Q x yout tout) (T := fun tin k' => exists (x : X), P x tin /\ g x <= k').
-
hnf.
setoid_rewrite TripleT_iff in H1.
unfold Triple_TRel in *.
intros tin k' outc HLoop x Hx.
specialize H1 with (x := x) as (H1&H1').
setoid_rewrite Triple_iff in H1.
unfold Triple_Rel, Realise in H1; clear H1'.
firstorder.
-
hnf.
setoid_rewrite TripleT_iff in H1.
unfold Triple_TRel in *.
intros tin k' (x&H&Hk).
specialize H1 with (x := x) as (H1&H1').
unfold Triple_TRel, TerminatesIn in H1'; clear H1.
firstorder.
}
{
clear H1.
apply WhileCoInduction; intros.
hnf in HT.
destruct HT as (x&HPx&Hk).
exists (g x).
split.
-
exists x.
split; eauto.
-
intros [ y | ].
+
clear H3.
intros tmid H.
specialize H with (1 := HPx).
specialize H2 with (1 := HPx) (2 := H) as (H3&H3').
lia.
+
clear H2.
intros tmid H.
specialize H with (1 := HPx).
specialize H3 with (1 := HPx) (2 := H) as (x'&H2&H2').
exists (f x').
unfold Triple_TRel.
repeat split.
*
exists x'.
split; [assumption|lia].
*
lia.
}
}
