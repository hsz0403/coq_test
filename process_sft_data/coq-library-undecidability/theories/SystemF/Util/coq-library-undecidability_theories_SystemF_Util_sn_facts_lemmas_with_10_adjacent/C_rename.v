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

Lemma E_beta s t ρ : E (subst_poly_type (t .: poly_var) s) ρ == E s (V t ρ .: ρ).
Proof.
intros P.
Admitted.

Lemma C_ext : Proper (pointwise_relation _ eq ==> eq ==> eq ==> iff) C.
Proof.
split; repeat intros ?; subst.
now rewrite <- H.
Admitted.

Lemma C_scons s Γ ρ σ P : E s ρ P -> C Γ ρ σ -> C (s .: Γ) ρ (P .: σ).
Proof.
intros HE HC.
hnf.
intros [].
eassumption.
Admitted.

Lemma C_up s Γ ρ σ : C Γ ρ σ -> C (s .: Γ) ρ (up_term_term σ).
Proof.
intros H.
eapply C_scons.
eapply R_var.
Admitted.

Lemma E2_ind s t ρ1 ρ2 p : (forall P Q, E s ρ1 P -> E t ρ2 Q -> (forall P', step P P' -> p P' Q) -> (forall Q', step Q Q' -> p P Q') -> p P Q) -> forall P Q, E s ρ1 P -> E t ρ2 Q -> p P Q.
Proof.
intros H P Q.
induction 1 in Q |- *.
induction 1.
Admitted.

Lemma E_app s t P Q ρ : E (poly_arr s t) ρ P -> E s ρ Q -> E t ρ (app P Q).
Proof.
revert P Q.
eapply E2_ind.
intros P Q nP nQ IHP IHQ.
econstructor.
inversion 1.
intros R Hst.
inv Hst; eauto.
destruct nP.
Admitted.

Lemma E_lam s t s' ρ P : sn P -> (forall ξ1 ξ2 Q, E s ρ Q -> E t ρ (subst_term (ξ1 >> poly_var) (Q .: ξ2 >> var) P)) -> E (poly_arr s t) ρ (abs s' P).
Proof.
induction 1 as [P _ IH].
intros H.
econstructor.
-
intros _.
rewrite K_arr.
eauto.
-
intros Q Hst.
inv Hst.
eapply IH; eauto.
intros.
Admitted.

Lemma E_tapp s t ρ P r : E (poly_abs s) ρ P -> E (subst_poly_type (t .: poly_var) s) ρ (ty_app P r).
Proof.
induction 1 as [P H IH H2].
eapply E_beta.
econstructor.
inversion 1.
intros Q Hst.
inv Hst.
-
specialize (H eq_refl).
rewrite K_all in H.
eauto.
-
eapply H2 in H4.
Admitted.

Lemma E_tlam s ρ P : sn P -> (forall ξ p t, E s (p .: ρ) (subst_term (t .: ξ >> poly_var) var P)) -> E (poly_abs s) ρ (ty_abs P).
Proof.
induction 1 as [P _ IH].
intros H.
econstructor.
-
rewrite K_all.
intros _.
eapply H.
-
intros Q Hst.
inv Hst.
eapply IH.
eauto.
intros ξ p t.
Admitted.

Lemma fundamental {Γ s P} : typing Γ P s -> forall σ τ ρ, C (fun n => match List.nth_error Γ n with Some x => x | _ => poly_abs (poly_var 0) end) ρ τ -> E s ρ (subst_term σ τ P).
Proof.
induction 1 as [Γ n s H | | Γ | | ]; intros σ τ ρ HC.
-
specialize (HC n).
cbn in HC.
rewrite H in HC.
eapply HC.
-
cbn.
eapply E_app; eauto.
-
eapply E_lam; fold subst_term.
+
eapply R_sn.
eapply IHtyping.
eapply C_ext.
4:{
eapply C_up, HC.
}
all: try reflexivity.
now intros [].
+
intros ξ1 ξ2 Q HQ.
match goal with [ |- E _ _ ?R] => replace R with (subst_term (σ >> ren_poly_type ξ1) (Q .: τ >> ren_term ξ1 ξ2) P) end.
*
eapply IHtyping.
eapply C_ext.
4:{
eapply C_scons.
eauto.
eapply C_rename, HC.
}
all: try reflexivity.
intros []; cbn; try reflexivity.
*
asimpl.
eapply ext_term.
intros.
asimpl.
--
erewrite rinst_inst_poly_type; reflexivity.
--
intros [].
reflexivity.
asimpl.
erewrite rinst_inst_term; try reflexivity.
now asimpl.
-
cbn.
eapply E_tapp; eauto.
-
cbn.
eapply E_tlam.
+
specialize (IHtyping (up_poly_type_poly_type σ) (τ >> ren_term shift id) ((fun _ => False) .: ρ)).
eapply R_sn.
refine (IHtyping _).
intros n.
rewrite Facts.nth_error_map.
destruct List.nth_error eqn:Eq.
*
cbn.
asimpl.
eapply E_weaken.
specialize (HC n).
cbn in HC.
rewrite Eq in HC.
eapply R_ren, HC.
*
unfold ssrfun.Option.map, ssrfun.Option.bind, ssrfun.Option.apply.
eapply R_ren.
specialize (HC n).
cbn in HC.
rewrite Eq in HC.
eapply HC.
+
intros ξ p t.
asimpl.
eapply IHtyping.
intros n.
asimpl.
eapply R_ext.
2:reflexivity.
2:{
eapply E_weaken.
erewrite <- rinst_inst_term; try reflexivity.
eapply R_ren.
eapply HC.
}
*
f_equal.
rewrite Facts.nth_error_map.
Admitted.

Lemma SN {Gamma P t} : typing Gamma P t -> sn P.
Proof.
intros Htp.
pose proof (fundamental Htp poly_var var (fun _ _ => False)).
asimpl in H.
eapply R_sn, H.
intros n.
Admitted.

Lemma typing_normal_form {Gamma P t} : typing Gamma P t -> exists Q, normal_form Q /\ typing Gamma Q t.
Proof.
intros H.
destruct (sn_normal _ _ _ H (SN H)) as (Q & H1 & H2).
exists Q.
split.
eassumption.
Admitted.

Lemma C_rename Γ ρ σ ξ1 ξ2 : C Γ ρ σ -> C Γ ρ (σ >> ren_term ξ1 ξ2).
Proof.
intros H ?.
eapply R_ren, H.
