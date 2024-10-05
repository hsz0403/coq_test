From Undecidability.L Require Import Util.L_facts Seval.
Require Import RelationClasses.
Inductive timeBS : nat -> term -> term -> Prop := timeBSVal s : timeBS 0 (lam s) (lam s) | timeBSBeta (s s' t t' u : term) i j k l: timeBS i s (lam s') -> timeBS j t (lam t') -> timeBS k (subst s' 0 (lam t')) u -> l = (i+j+1+k) -> timeBS l (app s t) u.
Module Leftmost.
Reserved Notation "s '≻lm' t" (at level 50).
Inductive step_lm : term -> term -> Prop := | step_lmApp s t : app (lam s) (lam t) ≻lm subst s 0 (lam t) | step_lmAppR s t t' : t ≻lm t' -> app (lam s) t ≻lm app (lam s) t' | step_lmAppL s s' t : s ≻lm s' -> app s t ≻lm app s' t where "s '≻lm' t" := (step_lm s t).
Hint Constructors step_lm : core.
Ltac inv_step_lm := match goal with | H : step_lm (lam _) _ |- _ => inv H | H : step_lm (var _) _ |- _ => inv H | H : star step_lm (lam _) _ |- _ => inv H | H : star step_lm (var _) _ |- _ => inv H end.
Instance pow_step_lm_congL k: Proper ((pow step_lm k) ==> eq ==> (pow step_lm k)) app.
Proof.
intros s t R u ? <-.
revert s t R u.
induction k;cbn in *;intros ? ? R ?.
congruence.
destruct R as [s' [R1 R2]].
exists (app s' u).
firstorder.
Instance pow_step_lm_congR k: Proper (eq ==>(pow step_lm k) ==> (pow step_lm k)) (fun s t => app (lam s) t).
Proof.
intros s ? <- t u R.
revert s t u R.
induction k;cbn in *;intros ? ? ? R.
congruence.
destruct R as [t' [R1 R2]].
exists (app (lam s) t').
firstorder.
Instance step_lm_step: subrelation step_lm step.
Proof.
induction 1;eauto using step.
Definition redWithMaxSizeL := redWithMaxSize size step_lm.
Inductive spaceBS : nat -> term -> term -> Prop := spaceBSVal s : spaceBS (size (lam s)) (lam s) (lam s) | spaceBSBeta (s s' t t' u : term) m1 m2 m3 m: spaceBS m1 s (lam s') -> spaceBS m2 t (lam t') -> spaceBS m3 (subst s' 0 (lam t')) u -> m = max (m1 + 1 + size t) (max (size (lam s') + 1 + m2) m3) -> spaceBS m (app s t) u.
End Leftmost.
Definition hasTime k s := exists t, evalIn k s t.
Definition hasSpace m s := maxP (fun m => exists s', s >* s' /\ m = size s' ) m.

Lemma spaceBS_correct_lm s t m: spaceBS m s t <-> redWithMaxSizeL m s t /\ lambda t.
Proof.
split.
-
intros R.
induction R.
+
repeat econstructor.
+
destruct IHR1 as (R1'&?).
destruct IHR2 as (R2'&?).
destruct IHR3 as (R3'&?).
split;[|firstorder].
subst m.
eapply redWithMaxSize_trans with (t:=app (lam s') t).
{
eapply redWithMaxSizeL_congL.
eassumption.
reflexivity.
}
eapply redWithMaxSize_trans with (t:=app (lam s') (lam t')).
{
eapply redWithMaxSizeL_congR.
eassumption.
reflexivity.
}
econstructor.
constructor.
eassumption.
reflexivity.
reflexivity.
specialize (spaceBS_ge R2) as [_ H3];cbn in H3.
cbn - [plus].
repeat eapply Nat.max_case_strong;lia.
-
intros (R&H).
induction R as [t | s s' t m].
+
inv H;rename x into t.
eauto using spaceBS.
+
inv H;rename m' into m.
eapply step_lm_evaluatesSpace.
eassumption.
eauto.
