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

Lemma ksoundness A (phi : form) : A ⊢I phi -> kvalid_ctx A phi.
Proof.
intros Hprv D M.
remember intu as s.
induction Hprv; subst; cbn; intros u rho HA.
all: repeat (clean_ksoundness + discriminate).
all: (eauto || comp; eauto).
-
intros v Hr Hpi.
eapply IHHprv.
intros ? []; subst; eauto using ksat_mon.
-
eapply IHHprv1.
3: eapply IHHprv2.
all: eauto.
apply M.
-
intros d.
apply IHHprv.
intros psi [psi' [<- Hp]] % in_map_iff.
cbn.
rewrite ksat_comp.
apply HA, Hp.
-
rewrite ksat_comp.
eapply ksat_ext.
2: eapply (IHHprv u rho HA (eval rho t)).
unfold funcomp.
now intros [].
-
now apply IHHprv in HA.
