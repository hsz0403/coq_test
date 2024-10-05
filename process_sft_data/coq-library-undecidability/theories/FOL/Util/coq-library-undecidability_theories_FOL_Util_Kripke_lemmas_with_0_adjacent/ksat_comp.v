From Undecidability Require Import FOL.Util.Deduction FOL.Util.Tarski FOL.Util.Syntax.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Local Notation vec := Vector.t.
Section Kripke.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Section Model.
Variable domain : Type.
Class kmodel := { nodes : Type ; reachable : nodes -> nodes -> Prop ; reach_refl u : reachable u u ; reach_tran u v w : reachable u v -> reachable v w -> reachable u w ; k_interp : interp domain ; k_P : nodes -> forall P : preds, Vector.t domain (ar_preds P) -> Prop ; (* k_Bot : nodes -> Prop ; *) mon_P : forall u v, reachable u v -> forall P (t : Vector.t domain (ar_preds P)), k_P u t -> k_P v t; }.
Variable M : kmodel.
Fixpoint ksat {ff : falsity_flag} u (rho : nat -> domain) (phi : form) : Prop := match phi with | atom P v => k_P u (Vector.map (@eval _ _ _ k_interp rho) v) | falsity => False | bin Impl phi psi => forall v, reachable u v -> ksat v rho phi -> ksat v rho psi | quant All phi => forall j : domain, ksat u (j .: rho) phi end.
End Model.
Notation "rho '⊩(' u ')' phi" := (ksat _ u rho phi) (at level 20).
Notation "rho '⊩(' u , M ')' phi" := (@ksat _ M _ u rho phi) (at level 20).
Arguments ksat {_ _ _} _ _ _, _ _ _ _ _ _.
Hint Resolve reach_refl : core.
Section Substs.
Variable D : Type.
Context {M : kmodel D}.
End Substs.
Context {ff : falsity_flag}.
Definition kvalid_ctx A phi := forall D (M : kmodel D) u rho, (forall psi, psi el A -> ksat u rho psi) -> ksat u rho phi.
Definition kvalid phi := forall D (M : kmodel D) u rho, ksat u rho phi.
Definition ksatis phi := exists D (M : kmodel D) u rho, ksat u rho phi.
End Kripke.
Notation "rho '⊩(' u ')' phi" := (ksat u rho phi) (at level 20).
Notation "rho '⊩(' u , M ')' phi" := (@ksat _ _ _ M _ u rho phi) (at level 20).
Arguments ksat {_ _ _ _ _} _ _ _, {_ _ _} _ {_} _ _ _.
Section KSoundness.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ff : falsity_flag}.
Ltac clean_ksoundness := match goal with | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl) | [ H : (?A -> ?B), H2 : (?A -> ?B) -> _ |- _] => specialize (H2 H) end.
End KSoundness.
Section ToTarski.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Program Instance interp_kripke {domain} (I : interp domain) : kmodel domain := {| nodes := unit ; reachable u v := True |}.
Next Obligation.
-
now apply I in X.
Defined.
End ToTarski.

Lemma ksat_comp {ff : falsity_flag} u rho xi phi : rho ⊩(u,M) phi[xi] <-> (xi >> eval rho (I := @k_interp _ M)) ⊩(u,M) phi.
Proof.
induction phi as [ | b P v | | ] in rho, xi, u |-*; comp.
-
tauto.
-
erewrite Vector.map_map.
erewrite Vector.map_ext.
2: apply eval_comp.
reflexivity.
-
destruct b0.
setoid_rewrite IHphi1.
now setoid_rewrite IHphi2.
-
destruct q.
setoid_rewrite IHphi.
split; intros H d; eapply ksat_ext.
2, 4: apply (H d).
all: intros []; cbn; trivial; unfold funcomp; now erewrite eval_comp.
