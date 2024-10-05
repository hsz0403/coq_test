Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
Require Import Undecidability.SystemF.Util.typing_facts Undecidability.SystemF.Util.term_facts.
Inductive step : term -> term -> Prop := | step_beta s P Q : step (app (abs s P) Q) (subst_term poly_var (scons Q var) P) | step_ty_beta P s : step (ty_app (ty_abs P) s) (subst_term (scons s poly_var) var P) | step_appL P P' Q : step P P' -> step (app P Q) (app P' Q) | step_appR P P' Q : step P P' -> step (app Q P) (app Q P') | step_ty_app P P' s : step P P' -> step (ty_app P s) (ty_app P' s) | step_lam s P P' : step P P' -> step (abs s P) (abs s P') | step_ty_lam P P' : step P P' -> step (ty_abs P) (ty_abs P').
Inductive sn x : Prop := | SNI : (forall y, step x y -> sn y) -> sn x.
Hint Constructors step normal_form head_form : core.
Require Import Coq.Relations.Relation_Operators.
Ltac inv_step := match goal with [ H : step ?P ?Q |- _] => inversion H; subst; clear H; try now firstorder end.
Ltac now_asimpl := asimpl; ( (reflexivity || eapply ext_term; now intros []; repeat asimpl) || f_equal; (reflexivity || eapply ext_term; now intros []; repeat asimpl)).
Require Import Coq.Program.Equality.
Ltac inv H := inversion H; subst; clear H.
Definition nf P := match P with abs s P => normal_form P | ty_abs P => normal_form P | P => head_form P end.

Lemma step_subst_inv P Q σ τ : step (subst_term σ (τ >> var) P) Q -> exists P', step P P' /\ subst_term σ (τ >> var) P' = Q.
Proof with eexists; split; [eauto | now_asimpl].
intros H.
dependent induction H; rename x into Eqn.
-
destruct P; inv Eqn.
destruct P1; inv H0...
-
destruct P; inv Eqn.
destruct P; inv H0...
-
destruct P; inv Eqn.
destruct (IHstep _ _ _ eq_refl) as (P1' & H1 & <-)...
-
destruct P; inv Eqn.
destruct (IHstep _ _ _ eq_refl) as (P1' & H1 & <-)...
-
destruct P; inv Eqn.
destruct (IHstep _ _ _ eq_refl) as (P1' & H1 & <-)...
-
destruct P; inv Eqn.
edestruct (IHstep P (up_term_poly_type σ) (0 .: τ >> shift)) as (P1' & H1 & <-).
now_asimpl.
exists (abs p P1').
split.
eauto.
now_asimpl.
-
destruct P; inv Eqn.
destruct (IHstep _ _ _ eq_refl) as (P1' & H1 & <-)...
