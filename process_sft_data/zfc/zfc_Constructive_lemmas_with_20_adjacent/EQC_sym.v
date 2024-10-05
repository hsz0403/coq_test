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

Definition EQC : Ens -> Ens -> Type.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
refine (prod_t _ _).
exact (forall x : A, depprod _ (fun y : B => eq1 x (g y))).
Admitted.

Definition CIN : Ens -> Ens -> Type.
simple induction 2.
intros.
Admitted.

Definition CINC : Ens -> Ens -> Type.
intros E1 E2.
Admitted.

Theorem EQC_refl : forall E : Ens, EQC E E.
simple induction E.
intros A f HR.
simpl in |- *.
split; intros.
exists x; auto with zfc.
Admitted.

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
Admitted.

Theorem EQC_INC : forall E E' : Ens, EQC E E' -> CINC E E'.
simple induction E; simple induction E'; simpl in |- *; intros; unfold CINC in |- *; simpl in |- *.
elim X1; intros.
elim X2; intros.
elim (a x); intros.
Admitted.

Theorem CINC_EQC : forall E E' : Ens, CINC E E' -> CINC E' E -> EQC E E'.
simple induction E; simple induction E'; unfold CINC in |- *; simpl in |- *; intros; split; intros.
apply X1.
exists x; auto with zfc.
cut (depprod A (fun x : A => EQC (e0 y) (e x))); try (simple induction 1; intros x p; exists x; auto with zfc).
Admitted.

Theorem CIN_sound_left : forall E E' E'' : Ens, EQC E E' -> CIN E E'' -> CIN E' E''.
simple induction E''; simpl in |- *; intros.
elim X1; intros y p; exists y.
Admitted.

Theorem CIN_sound_right : forall E E' E'' : Ens, EQC E' E'' -> CIN E E' -> CIN E E''.
simple induction E'; simple induction E''; simpl in |- *; intros.
Admitted.

Theorem CINC_refl : forall E : Ens, CINC E E.
Admitted.

Theorem CINC_tran : forall E E' E'' : Ens, CINC E E' -> CINC E' E'' -> CINC E E''.
Admitted.

Theorem CINC_sound_left : forall E E' E'' : Ens, EQC E E' -> CINC E E'' -> CINC E' E''.
simple induction E''; unfold CINC in |- *; simpl in |- *; intros A f XR e X1 E0 i; apply X1.
Admitted.

Theorem CINC_sound_right : forall E E' E'' : Ens, EQC E' E'' -> CINC E E' -> CINC E E''.
simple induction E'; simple induction E''; unfold CINC in |- *; simpl in |- *; intros.
elim (X2 E0); try assumption; intros.
elim X1; intros XA XB; elim (XA x); intros.
Admitted.

Theorem tout_vide_est_VideC : forall E : Ens, (forall E' : Ens, CIN E' E -> F) -> EQC E Vide.
unfold Vide in |- *; simple induction E; simpl in |- *; intros A e X H; split.
intros; elim (H (e x)); auto with zfc.
exists x; auto with zfc.
Admitted.

Theorem Paire_sound_leftC : forall A A' B : Ens, EQC A A' -> EQC (Paire A B) (Paire A' B).
unfold Paire in |- *.
simpl in |- *.
intros; split.
simple induction x.
exists true; auto with zfc.
exists false; auto with zfc.
simple induction y; simpl in |- *.
exists true; auto with zfc.
Admitted.

Theorem Paire_sound_rightC : forall A B B' : Ens, EQC B B' -> EQC (Paire A B) (Paire A B').
unfold Paire in |- *; simpl in |- *; intros; split.
simple induction x.
exists true; auto with zfc.
exists false; auto with zfc.
simple induction y.
exists true; auto with zfc.
Admitted.

Theorem CIN_Paire_left : forall E E' : Ens, CIN E (Paire E E').
Admitted.

Theorem CIN_Paire_right : forall E E' : Ens, CIN E' (Paire E E').
Admitted.

Theorem Paire_CIN : forall E E' A : Ens, CIN A (Paire E E') -> sum_t (EQC A E) (EQC A E').
Admitted.

Theorem CIN_Sing : forall E : Ens, CIN E (Sing E).
Admitted.

Theorem CIN_Sing_EQ : forall E E' : Ens, CIN E (Sing E') -> EQC E E'.
Admitted.

Theorem EQC_EQ : forall E E' : Ens, EQC E E' -> EQ E E'.
simple induction E; intros A f ra; simple induction E'; intros B g rb; simpl in |- *; simple induction 1; intros H1 H2; split.
intros a; elim (H1 a); intros b; intros; exists b; auto with zfc.
Admitted.

Theorem CIN_IN : forall E E' : Ens, CIN E E' -> IN E E'.
simple induction E; intros A f ra; simple induction E'; intros B g rb; simple induction 1; intros a; unfold IN in |- *; exists a; auto with zfc.
Admitted.

Theorem EQC_EXType : forall E E' : Ens, EQC E E' -> forall a : pi1 E, depprod (pi1 E') (fun b : pi1 E' => EQC (pi2 E a) (pi2 E' b)).
simple induction E; simple induction E'; simpl in |- *.
intros.
elim X1; intros.
elim (a0 a); intros.
Admitted.

Theorem CIN_EXType : forall E E' : Ens, CIN E' E -> depprod (pi1 E) (fun a : pi1 E => EQC E' (pi2 E a)).
simple induction E; simpl in |- *.
intros A f r.
simple induction 1; simpl in |- *.
intros.
Admitted.

Theorem EQC_sym : forall E1 E2 : Ens, EQC E1 E2 -> EQC E2 E1.
simple induction E1; simple induction E2; simpl in |- *; intros.
elim X1; intros; split; intros.
elim (b x); intros.
exists x0; auto with zfc.
elim (a y); intros; exists x; auto with zfc.
