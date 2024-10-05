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
firstorder.
