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

Instance pow_step_lm_congL k: Proper ((pow step_lm k) ==> eq ==> (pow step_lm k)) app.
Proof.
intros s t R u ? <-.
revert s t R u.
induction k;cbn in *;intros ? ? R ?.
congruence.
destruct R as [s' [R1 R2]].
exists (app s' u).
Admitted.

Instance pow_step_lm_congR k: Proper (eq ==>(pow step_lm k) ==> (pow step_lm k)) (fun s t => app (lam s) t).
Proof.
intros s ? <- t u R.
revert s t u R.
induction k;cbn in *;intros ? ? ? R.
congruence.
destruct R as [t' [R1 R2]].
exists (app (lam s) t').
Admitted.

Instance step_lm_step: subrelation step_lm step.
Proof.
Admitted.

Lemma redWithMaxSizeL_congL m m' s s' t: redWithMaxSizeL m s s' -> m' = (1 + m + size t) -> redWithMaxSizeL m' (app s t) (app s' t).
Proof.
intros R Heq.
induction R as [s | s s'] in m',t,Heq |-* .
-
apply redWithMaxSizeR.
cbn.
lia.
-
eapply redWithMaxSizeC.
now eauto using step_lm.
apply IHR.
reflexivity.
subst m m'.
cbn.
Admitted.

Lemma redWithMaxSizeL_congR m m' s t t': redWithMaxSizeL m t t' -> m' = (1 + m + size (lam s)) -> redWithMaxSizeL m' (app (lam s) t) (app (lam s) t').
Proof.
intros R Heq.
induction R as [t | t t'] in m',s,Heq |-* .
-
apply redWithMaxSizeR.
cbn in *.
lia.
-
eapply redWithMaxSizeC.
now eauto using step_lm.
apply IHR.
reflexivity.
subst m m'.
cbn -[plus].
Admitted.

Lemma step_lm_evaluatesIn s s' t k: s ≻lm s' -> timeBS k s' t -> timeBS (S k) s t.
Proof.
intros H; induction H in t,k|-*; intros; try inv H0; eauto 20 using timeBS.
eapply IHstep_lm in H4.
econstructor; eauto.
Admitted.

Lemma timeBS_correct_lm s t k: (timeBS k s t <-> pow step_lm k s t /\ lambda t).
Proof.
split.
-
intros R.
induction R.
+
unfold pow;cbn.
eauto.
+
destruct IHR1 as [R1'].
destruct IHR2 as [R2'].
destruct IHR3 as [R3'].
split;[|assumption].
subst l.
replace (i+j+1+k) with (i+(j+(1+k))) by lia.
eapply pow_add.
eexists;split.
eapply pow_step_lm_congL;now eauto.
eapply pow_add.
eexists;split.
eapply pow_step_lm_congR;now eauto.
eapply pow_add.
eexists;split.
eapply (rcomp_1 step_lm).
eauto.
eauto.
-
intros [R lt].
induction k in s,t,R,lt,R|-*.
+
inv R.
inv lt.
constructor.
+
change (S k) with (1+k) in R.
eapply pow_add in R as (?&R'&?).
eapply (rcomp_1 step_lm) in R'.
Admitted.

Lemma spaceBS_ge s t m: spaceBS m s t -> size s<= m /\ size t <= m.
Proof.
induction 1.
lia.
subst m.
cbn -[plus].
Admitted.

Lemma step_lm_evaluatesSpace s s' t m: s ≻lm s' -> spaceBS m s' t -> spaceBS (max (size s) m) s t.
Proof.
intros H; induction H in t,m|-*; intros H'.
-
inv H'.
+
destruct s;inv H1.
destruct (Nat.eqb_spec n 0);inv H0.
all:repeat econstructor.
all:cbn -[plus].
all:(repeat apply Nat.max_case_strong;try lia).
+
destruct s;inv H.
now destruct (Nat.eqb_spec n 0);inv H0.
econstructor.
1,2:econstructor.
cbn.
econstructor.
1-4:now eauto.
cbn -[plus].
(repeat apply Nat.max_case_strong;intros;try lia).
-
inv H'.
inv H2.
specialize (spaceBS_ge H3) as [? ?].
specialize (spaceBS_ge H3) as [? ?].
apply IHstep_lm in H3.
specialize (spaceBS_ge H5) as [? ?].
specialize (spaceBS_ge H3) as [_ H''].
econstructor;[now eauto using spaceBS..|].
revert H''.
cbn -[plus] in *.
(repeat apply Nat.max_case_strong;intros;try lia).
-
inv H'.
specialize (spaceBS_ge H2) as [? ?].
eapply IHstep_lm in H2.
specialize (spaceBS_ge H2) as [_ H7].
specialize (spaceBS_ge H3) as [? ?].
econstructor.
1-3:eassumption.
revert H7.
cbn -[plus] in *.
Admitted.

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
Admitted.

Lemma step_lm_functional : functional step_lm.
Proof.
intros s t t' H1 H2.
induction H1 in t',H2|-*;inv H2;try easy;try congruence.
all:f_equal.
all:apply IHstep_lm;eauto.
