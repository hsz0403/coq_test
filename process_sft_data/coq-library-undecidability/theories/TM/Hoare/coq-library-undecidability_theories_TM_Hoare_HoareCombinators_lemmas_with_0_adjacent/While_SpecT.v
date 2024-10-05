From Undecidability Require Import TMTac TM.Util.Prelim.
From Undecidability.TM Require Export Compound.Multi Combinators.Combinators.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister.

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
