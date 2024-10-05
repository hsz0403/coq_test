Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
From Undecidability.SystemF.Util Require Import typing_facts term_facts step.
Require Import Setoid Morphisms.
Set Default Proof Using "Type".
Definition pw_iff {X} p q := (forall x : X, p x <-> q x).
Notation "p == q" := (pw_iff p q) (at level 70).
Instance Equiv_pw_iff {X} : Equivalence (@pw_iff X).
Proof.
firstorder.
Ltac pw := repeat (apply pw; intros).
Definition active P := match P with | abs _ _ | ty_abs _ => true | _ => false end.
Definition tpred := term -> Prop.
Definition M (p : tpred) : tpred := fun P => forall ξ1 ξ2, p (ren_term ξ1 ξ2 P).
Inductive R (p : tpred) P : Prop := | RI : (active P = true -> M p P) -> (forall Q, step P Q -> R p Q) -> R p P.
Instance R_ext : Proper (pw_iff ==> eq ==> iff) R.
Proof.
intros p1 p2 Heq P ? ->.
split; induction 1 as [P H H1 H2].
-
econstructor.
intros H3 ξ1 ξ2.
eapply Heq.
now eapply H.
eauto.
-
econstructor.
intros H3 ξ1 ξ2.
eapply Heq.
now eapply H.
eauto.
Record model := mk_model { Var : tpred -> tpred ; Arr : tpred -> tpred -> tpred ; All : (tpred -> tpred) -> tpred ; Var_ext : Proper (pw_iff ==> pw_iff) Var ; Arr_ext : Proper (pw_iff ==> pw_iff ==> pw_iff) Arr ; All_ext : Proper (pointwise_relation _ pw_iff ==> pw_iff) All }.
Existing Instances Var_ext Arr_ext All_ext.
Section Evaluation.
Variable (M : model).
Fixpoint eval (ρ : nat -> tpred) (s : poly_type) : tpred := match s with | poly_var n => Var M (ρ n) | poly_arr s t => Arr M (eval ρ s) (eval ρ t) | poly_abs s => All M (fun d => eval (d .: ρ) s) end.
Instance eval_ext : Proper (pointwise_relation _ pw_iff ==> eq ==> pw_iff) eval.
Proof.
intros ρ1 ρ2 Heq s ? <-.
induction s in ρ1, ρ2, Heq |- *; cbn.
-
now rewrite (Heq n).
-
now rewrite IHs1, IHs2.
-
eapply All_ext.
intros d.
eapply IHs.
intros []; cbn; intuition.
Definition lift : model.
Proof using M.
refine (mk_model id (Arr M) (fun F => All M (Var M >> F)) _ _ _).
abstract firstorder.
abstract (intros p1 p2 H; eapply All_ext; intros P; eapply H).
Defined.
End Evaluation.
Definition D : model.
Proof.
refine {| Var := id ; Arr := fun p q P => match P with abs s P => forall Q, R p Q -> R q (subst_term poly_var (Q .: var) P) | _ => False end ; All := fun F P => match P with ty_abs P => forall p s, R (F p) (subst_term (s .: poly_var) var P) | _ => False end |}.
-
abstract firstorder.
-
abstract (intros p1 p2 Heq1 p1' p2' Heq2 []; cbn; try tauto; pw; now rewrite Heq1, Heq2).
-
abstract (intros F1 F2 Heq []; cbn; try tauto; pw; now rewrite (Heq x)).
Defined.
Notation V s ρ := (eval D ρ s).
Notation K s ρ := (M (V s ρ)).
Notation E s ρ := (R (V s ρ)).
Definition C (Γ : nat -> poly_type) (ρ : nat -> tpred) : (nat -> term) -> Prop := fun σ => forall n, E (Γ n) ρ (σ n).

Instance Equiv_pw_iff {X} : Equivalence (@pw_iff X).
Proof.
Admitted.

Lemma pw {X : Type} P Q : (forall x : X, P x <-> Q x) -> (forall x, P x) <-> (forall x, Q x).
Proof.
Admitted.

Instance R_ext : Proper (pw_iff ==> eq ==> iff) R.
Proof.
intros p1 p2 Heq P ? ->.
split; induction 1 as [P H H1 H2].
-
econstructor.
intros H3 ξ1 ξ2.
eapply Heq.
now eapply H.
eauto.
-
econstructor.
intros H3 ξ1 ξ2.
eapply Heq.
now eapply H.
Admitted.

Instance eval_ext : Proper (pointwise_relation _ pw_iff ==> eq ==> pw_iff) eval.
Proof.
intros ρ1 ρ2 Heq s ? <-.
induction s in ρ1, ρ2, Heq |- *; cbn.
-
now rewrite (Heq n).
-
now rewrite IHs1, IHs2.
-
eapply All_ext.
intros d.
eapply IHs.
Admitted.

Lemma eval_ren ξ s ρ : eval ρ (ren_poly_type ξ s) == eval (ξ >> ρ) s.
Proof.
induction s in ξ, ρ |- *; cbn.
-
reflexivity.
-
now rewrite IHs1, IHs2.
-
eapply All_ext.
intros d.
rewrite IHs.
eapply eval_ext.
now intros [].
Admitted.

Lemma eval_weaken s ρ d : eval (d .: ρ) (ren_poly_type shift s) == eval ρ s.
Proof.
Admitted.

Definition lift : model.
Proof using M.
refine (mk_model id (Arr M) (fun F => All M (Var M >> F)) _ _ _).
abstract firstorder.
Admitted.

Lemma eval_subst (M : model) σ s ρ : eval M ρ (subst_poly_type σ s) == eval (lift M) (σ >> eval M ρ) s.
Proof.
induction s in σ, ρ |- *; cbn.
-
reflexivity.
-
now rewrite IHs1, IHs2.
-
eapply All_ext.
intros d.
rewrite IHs.
asimpl.
eapply eval_ext; try reflexivity.
intros [].
reflexivity.
Admitted.

Lemma eval_beta (M : model) s t ρ : eval M ρ (subst_poly_type (t .: poly_var) s) == eval (lift M) (eval M ρ t .: ρ >> Var M) s.
Proof.
rewrite eval_subst.
eapply eval_ext.
now intros [].
Admitted.

Definition D : model.
Proof.
refine {| Var := id ; Arr := fun p q P => match P with abs s P => forall Q, R p Q -> R q (subst_term poly_var (Q .: var) P) | _ => False end ; All := fun F P => match P with ty_abs P => forall p s, R (F p) (subst_term (s .: poly_var) var P) | _ => False end |}.
-
abstract firstorder.
-
abstract (intros p1 p2 Heq1 p1' p2' Heq2 []; cbn; try tauto; pw; now rewrite Heq1, Heq2).
-
Admitted.

Lemma R_step p P Q : step P Q -> R p P -> R p Q.
Proof.
intros ? [].
Admitted.

Lemma R_var p n : R p (var n).
Proof.
econstructor.
intros [=].
intros Q H.
Admitted.

Lemma R_ren ξ1 ξ2 p P : R p P -> R p (ren_term ξ1 ξ2 P).
Proof.
induction 1 as [P H H0 H1].
econstructor.
-
intros HnP ξ'1 ξ'2.
asimpl.
eapply H.
now destruct P.
-
intros Q.
erewrite rinst_inst_term; try reflexivity.
intros (P' & H2 & <-) % step_subst_inv.
erewrite <- rinst_inst_term; try reflexivity.
Admitted.

Lemma K_var n ρ P : K (poly_var n) ρ P = forall ξ1 ξ2, ρ n (ren_term ξ1 ξ2 P).
Proof.
Admitted.

Lemma K_arr s t ρ u P : K (poly_arr s t) ρ (abs u P) <-> forall ξ1 ξ2 Q, E s ρ Q -> E t ρ (subst_term (ξ1 >> poly_var) (Q .: ξ2 >> var) P).
Proof.
unfold M.
cbn.
pw.
asimpl.
eapply R_ext.
reflexivity.
Admitted.

Lemma K_all s ρ P : K (poly_abs s) ρ (ty_abs P) <-> forall ξ p t, E s (p .: ρ) (subst_term (t .: ξ >> poly_var) var P).
Proof.
unfold M.
split.
-
intros H ξ p t.
specialize (H ξ id p t).
fold ren_term in H.
eapply R_ext.
3:eapply H.
reflexivity.
now_asimpl.
-
intros H ξ1 ξ2 p t.
specialize (H ξ1 p t).
pose proof (Hren := R_ren id ξ2 _ _ H).
asimpl in Hren.
eapply R_ext.
3:eapply Hren.
reflexivity.
Admitted.

Lemma V_weaken s ρ p : V (ren_poly_type shift s) (p .: ρ) == V s ρ.
Proof.
Admitted.

Lemma K_weaken s ρ p : K (ren_poly_type shift s) (p .: ρ) == K s ρ.
Proof.
intros P.
pw.
Admitted.

Lemma E_weaken s ρ p : E (ren_poly_type shift s) (p .: ρ) == E s ρ.
Proof.
intros P.
eapply R_ext.
eapply V_weaken.
Admitted.

Lemma V_beta s t ρ : V (subst_poly_type (t .: poly_var) s) ρ == V s (V t ρ .: ρ).
Proof.
Admitted.

Lemma R_sn p P : R p P -> sn P.
Proof.
induction 1.
eauto using sn.
