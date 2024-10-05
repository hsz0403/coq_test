Set Implicit Arguments.
Require Import Morphisms Setoid.
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU.calculus Require Import prelim terms semantics.
Set Default Proof Using "Type".
Section Confluence.
Context {X: Const}.
Reserved Notation "s ≫ t" (at level 60).
Inductive par : exp X -> exp X -> Prop := | parVar x: var x ≫ var x | parConst c: const c ≫ const c | parLam s s': s ≫ s' -> (lambda s) ≫ lambda s' | parBeta s s' t t' u: s ≫ s' -> t ≫ t' -> u = beta s' t' -> (lambda s) t ≫ u | parApp s s' t t': s ≫ s' -> t ≫ t' -> s t ≫ s' t' where "s ≫ t" := (par s t).
Hint Constructors par : core.
Hint Immediate refl_par : core.
Global Instance refl_par_inst: Reflexive par.
Proof.
intros ?; eapply refl_par.
Global Instance par_lam_proper: Proper (star par ++> star par) lam.
Proof.
intros s s' H; induction H; eauto.
Global Instance par_app_proper: Proper (star par ++> star par ++> star par) app.
Proof.
intros s s' H; induction H; intros t t' H'; induction H'; eauto.
Global Instance sandwich_step: subrelation step par.
Proof.
intros ??; induction 1; eauto.
Global Instance sandwich_steps: subrelation par (star step).
Proof.
intros ??; induction 1; eauto.
-
rewrite IHpar; eauto.
-
rewrite IHpar1, IHpar2, stepBeta; eauto.
-
rewrite IHpar1, IHpar2; eauto.
Fixpoint rho (e: exp X) := match e with | var x => var x | const c => const c | lambda s => lambda (rho s) | app (lambda s) t => beta (rho s) (rho t) | app s t => (rho s) (rho t) end.
End Confluence.
Notation "s ≫ t" := (par s t) (at level 60).
Hint Resolve confluence_step tak_fun_rho : core.

Lemma refl_par: forall s, s ≫ s.
Proof.
induction s; eauto.
