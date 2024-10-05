Require Import Sets.
Require Import Axioms.
Definition EQC : Ens -> Ens -> Type.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
refine (prod_t _ _).
exact (forall x : A, depprod _ (fun y : B => eq1 x (g y))).
exact (forall y : B, depprod _ (fun x : A => eq1 x (g y))).
Defined.
Definition CIN : Ens -> Ens -> Type.
simple induction 2.
intros.
exact (depprod _ (fun y : A => EQC X (e y))).
Defined.
Definition CINC : Ens -> Ens -> Type.
intros E1 E2.
exact (forall E : Ens, CIN E E1 -> CIN E E2).
Defined.
Hint Resolve EQC_sym EQC_refl EQC_INC: zfc.
Hint Resolve CINC_EQC: zfc.
Inductive sum_t (A B : Type) : Type := | inl_t : A -> sum_t A B | inr_t : B -> sum_t A B.
Hint Resolve inl_t inr_t: zfc.
Hint Resolve CIN_Paire_left CIN_Paire_right: zfc.
Inductive depprod' (A : Type) (P : A -> Type) : Type := dep_i' : forall x : A, P x -> depprod' A P.

Theorem EQC_tran : forall E1 E2 E3 : Ens, EQC E1 E2 -> EQC E2 E3 -> EQC E1 E3.
simple induction E1; simple induction E2; simple induction E3; simpl in |- *; intros.
split; (elim X2; intros; elim X3; intros).
elim (a x); intros.
elim (a0 x0); intros.
exists x1.
apply X with (e0 x0); auto with zfc.
elim (b0 y); intros.
elim (b x); intros.
exists x0.
apply X with (e0 x); auto with zfc.
