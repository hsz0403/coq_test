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

Theorem CIN_Union : forall E E' E'' : Ens, CIN E' E -> CIN E'' E' -> CIN E'' (Union E).
simple induction E; intros A f r.
intros.
simpl in |- *.
elim (CIN_EXType (sup A f) E' X).
intros x e.
cut (EQC (pi2 (sup A f) x) E'); auto with zfc.
intros e1.
cut (CIN E'' (pi2 (sup A f) x)).
intros i1.
elim (CIN_EXType _ _ i1).
intros x0 e2.
simpl in x0.
exists (dep_i A (fun x : A => pi1 (f x)) x x0).
simpl in |- *.
exact e2.
Admitted.

Theorem CIN_CINC_Union : forall E E' : Ens, CIN E' E -> CINC E' (Union E).
unfold CINC in |- *; simple induction E; intros A f r.
unfold Union in |- *.
intros.
simpl in |- *.
elim (CIN_EXType (sup A f) E' X).
intro.
simpl in x.
intros.
simpl in p.
elim (CIN_EXType E' E0 X0).
cut (CIN E0 (f x)).
intros.
elim (CIN_EXType _ _ X1).
simpl in |- *.
intros.
exists (dep_i A (fun x : A => pi1 (f x)) x x1); auto with zfc.
Admitted.

Theorem Union_soundC : forall E E' : Ens, EQC E E' -> EQC (Union E) (Union E').
unfold Union in |- *.
simpl in |- *.
simple induction E; intros A f r; simple induction E'; intros A' f' r'.
simpl in |- *.
intros.
elim X; intros.
split.
simple induction x.
intros.
elim (a x0).
intros.
elim (EQC_EXType (f x0) (f' x1) p0 p).
intros.
exists (dep_i A' (fun x : A' => pi1 (f' x)) x1 x2).
simpl in |- *.
auto with zfc.
simple induction y; intros.
elim (b x); intros.
cut (EQC (f' x) (f x0)); auto with zfc.
intros e.
elim (EQC_EXType (f' x) (f x0) e p); intros.
exists (dep_i A (fun x0 : A => pi1 (f x0)) x0 x1).
Admitted.

Theorem Union_monC : forall E E' : Ens, CINC E E' -> CINC (Union E) (Union E').
unfold CINC in |- *; intros.
elim (Union_CIN E E0 X0); intros.
Admitted.

Theorem Union_CIN : forall E E' : Ens, CIN E' (Union E) -> depprod' _ (fun E1 : Ens => prod_t (CIN E1 E) (CIN E' E1)).
simple induction E; unfold Union in |- *; simpl in |- *; intros A f r.
simple induction 1.
simple induction x.
intros a b; simpl in |- *.
intros.
exists (f a).
split.
exists a; auto with zfc.
apply CIN_sound_left with (pi2 (f a) b); auto with zfc.
simpl in |- *.
generalize b; elim (f a); simpl in |- *.
intros.
exists b0; auto with zfc.
