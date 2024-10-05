Set Implicit Arguments.
From Undecidability.HOU Require Import calculus.prelim calculus.terms calculus.syntax std.std.
Require Import Morphisms Lia FinFun.
Set Default Proof Using "Type".
Section Semantics.
Context {X: Const}.
Implicit Types (s t: exp X) (delta: fin -> fin) (sigma: fin -> exp X).
Reserved Notation "s > t" (at level 70).
Inductive step : exp X -> exp X -> Prop := | stepBeta s s' t: beta s t = s' -> (lambda s) t > s' | stepLam s s': s > s' -> lambda s > lambda s' | stepAppL s s' t: s > s' -> s t > s' t | stepAppR s t t': t > t' -> s t > s t' where "s > t" := (step s t).
Notation "s >* t" := (star step s t) (at level 70).
Hint Constructors step star : core.
Notation "s ▷ t" := (evaluates step s t) (at level 60).
Notation normal := (Normal step).
Section CompatibilityProperties.
Global Instance lam_proper: Proper (star step ++> star step) lam.
Proof.
induction 1; eauto.
Global Instance app_proper: Proper (star step ++> star step ++> star step) app.
Proof.
intros x x' H1 y y' H2; induction H1; induction H2; eauto.
Global Instance ren_step_proper: Proper (eq ++> step ++> step) (@ren X).
Proof.
intros ? zeta -> s t H; now eapply ren_step.
Global Instance ren_steps_proper: Proper (eq ++> star step ++> star step) (@ren X).
Proof.
intros ? zeta -> s t H; now eapply ren_steps.
Global Instance subst_step_proper: Proper (eq ++> step ++> step) (@subst_exp X).
Proof.
intros ? zeta -> s t H; now eapply subst_step.
Global Instance subst_steps_proper: Proper (eq ++> star step ++> star step) (@subst_exp X).
Proof.
intros ? zeta -> s t H; now eapply subst_steps.
End CompatibilityProperties.
Section Normality.
Hint Resolve normal_var normal_const normal_lam_intro normal_lam_elim normal_app_l normal_app_r normal_app_intro : core.
Global Instance dec_normal: Dec1 (normal).
Proof.
intros s; unfold Dec; induction s; intuition.
all: try solve [right; contradict b; eauto].
destruct s1; intuition.
right; intros H; eapply H; eauto.
End Normality.
Hint Resolve normal_var normal_const normal_lam_intro normal_lam_elim normal_app_l normal_app_r normal_app_intro : core.
Hint Resolve head_atom : core.
Section InversionLemmas.
End InversionLemmas.
End Semantics.
Notation "s > t" := (step s t) (at level 70).
Notation "s >* t" := (star step s t) (at level 70).
Notation "s ▷ t" := (evaluates step s t) (at level 60).
Notation normal := (Normal step).
Hint Constructors step star : core.
Hint Resolve normal_var normal_const normal_lam_intro normal_app_intro : core.
Hint Resolve head_atom : core.

Lemma ren_step s t delta: s > t -> ren delta s > ren delta t.
Proof.
induction 1 in delta |-*; cbn; eauto.
econstructor.
subst.
Admitted.

Lemma ren_steps s t delta: s >* t -> ren delta s >* ren delta t.
Proof.
Admitted.

Lemma subst_step s t sigma: s > t -> sigma • s > sigma • t.
Proof.
induction 1 in sigma |-*; cbn; eauto.
-
econstructor.
subst.
Admitted.

Lemma normal_var x: normal (var x).
Proof.
Admitted.

Lemma normal_const c: normal (const c).
Proof.
Admitted.

Lemma normal_lam_intro s: normal s -> normal (lambda s).
Proof.
Admitted.

Lemma normal_lam_elim s: normal (lambda s) -> normal s.
Proof.
Admitted.

Lemma normal_app_l s t: normal (s t) -> normal s.
Proof.
Admitted.

Lemma normal_app_r s t: normal (s t) -> normal t.
Proof.
Admitted.

Lemma normal_app_not_lam s t: normal (s t) -> ~ isLam s.
Proof.
Admitted.

Lemma normal_app_intro s t: ~ isLam s -> normal s -> normal t -> normal (s t).
Proof.
intros; intros t' H2; inv H2; cbn in *; eauto.
Admitted.

Lemma normal_ren s delta: normal s -> normal (ren delta s).
Proof.
induction s in delta |-*; cbn; intuition.
eapply normal_app_intro; eauto.
destruct s1; cbn; eauto.
Admitted.

Lemma normal_subst s sigma: (forall x, ~ isLam (sigma x)) -> (forall x, normal (sigma x)) -> normal s -> normal (sigma • s).
Proof.
induction s in sigma |-*; intros H1 H2 N; cbn in *; intuition.
-
eapply normal_lam_intro, IHs; [| | now eapply normal_lam_elim].
+
intros []; cbn; intuition.
unfold funcomp in *.
eapply H1 with (x := n).
destruct sigma; cbn; intuition.
+
intros []; cbn; intuition.
now eapply normal_ren.
-
eapply normal_app_intro; eauto.
destruct s1; eauto.
Admitted.

Lemma subst_steps s t sigma: s >* t -> sigma • s >* sigma • t.
Proof.
induction 1; eauto using subst_step.
