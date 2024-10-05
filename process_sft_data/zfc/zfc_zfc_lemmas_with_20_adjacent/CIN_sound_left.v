Set Asymmetric Patterns.
Inductive Ens : Type := sup : forall A : Type, (A -> Ens) -> Ens.
Inductive EXType (P : Type) (Q : P -> Prop) : Prop := EXTypei : forall x : P, Q x -> EXType P Q.
Inductive prod_t (A B : Type) : Type := pair_t : A -> B -> prod_t A B.
Inductive depprod (A : Type) (P : A -> Type) : Type := dep_i : forall x : A, P x -> depprod A P.
Definition EQ : Ens -> Ens -> Prop.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
apply and.
exact (forall x : A, EXType _ (fun y : B => eq1 x (g y))).
exact (forall y : B, EXType _ (fun x : A => eq1 x (g y))).
Defined.
Definition IN (E1 E2 : Ens) : Prop := match E2 with | sup A f => EXType _ (fun y : A => EQ E1 (f y)) end.
Definition INC : Ens -> Ens -> Prop.
intros E1 E2.
exact (forall E : Ens, IN E E1 -> IN E E2).
Defined.
Hint Resolve EQ_sym EQ_refl EQ_INC: zfc.
Hint Resolve INC_EQ: zfc.
Inductive Un : Set := void : Un.
Inductive F : Set :=.
Definition Vide : Ens := sup F (fun f : F => match f return Ens with end).
Definition Paire : forall E E' : Ens, Ens.
intros.
apply (sup bool).
simple induction 1.
exact E.
exact E'.
Defined.
Hint Resolve Paire_sound_right Paire_sound_left: zfc.
Hint Resolve IN_Paire_left IN_Paire_right Vide_est_vide: zfc.
Definition Sing (E : Ens) := Paire E E.
Hint Resolve IN_Sing IN_Sing_EQ: zfc.
Hint Resolve Sing_sound: zfc.
Hint Resolve EQ_Sing_EQ: zfc.
Inductive sig (A : Type) (P : A -> Prop) : Type := exist : forall x : A, P x -> sig A P.
Definition Comp : Ens -> (Ens -> Prop) -> Ens.
simple induction 1; intros A f fr P.
apply (sup (sig A (fun x => P (f x)))).
simple induction 1; intros x p; exact (f x).
Defined.
Definition pi1 : Ens -> Type.
simple induction 1.
intros A f r.
exact A.
Defined.
Definition pi2 : forall E : Ens, pi1 E -> Ens.
simple induction E.
intros A f r.
exact f.
Defined.
Definition Union : forall E : Ens, Ens.
simple induction 1; intros A f r.
apply (sup (depprod A (fun x : A => pi1 (f x)))).
simple induction 1; intros a b.
exact (pi2 (f a) b).
Defined.
Definition Inter (E : Ens) : Ens := match E with | sup A f => sup _ (fun c : depprod _ (fun a : A => depprod _ (fun b : pi1 (f a) => forall x : A, IN (pi2 (f a) b) (f x))) => match c with | dep_i a (dep_i b p) => pi2 (f a) b end) end.
Definition Power (E : Ens) : Ens := match E with | sup A f => sup _ (fun P : A -> Prop => sup _ (fun c : depprod A (fun a : A => P a) => match c with | dep_i a p => f a end)) end.
Definition Couple (E E' : Ens) := Paire (Sing E) (Paire Vide (Sing E')).
Definition Prod (E E' : Ens) : Ens := match E, E' with | sup A f, sup A' f' => sup _ (fun c : prod_t A A' => match c with | pair_t a a' => Couple (f a) (f' a') end) end.
Hint Resolve Paire_sound_left Paire_sound_right: zfc.
Definition Succ (E : Ens) := Union (Paire E (Sing E)).
Inductive Ord : Ens -> Prop := | Oo : Ord Vide | So : forall E : Ens, Ord E -> Ord (Succ E) | Lo : forall E : Ens, (forall e : Ens, IN e E -> Ord e) -> Ord (Union E) | Eo : forall E E' : Ens, Ord E -> EQ E E' -> Ord E'.
Hint Resolve Oo So Lo: zfc.
Definition Nat : nat -> Ens.
simple induction 1; intros.
exact Vide.
exact (Succ X).
Defined.
Definition Omega : Ens := sup nat Nat.
Hint Resolve IN_Succ INC_Succ: zfc.
Hint Resolve Nat_IN_Omega: zfc.
Definition Alpha : Ens -> Ens.
simple induction 1; intros A f r.
apply Union.
apply (sup A).
intros a.
exact (Power (r a)).
Defined.
Definition collection := forall P : Ens -> Ens -> Prop, (forall x x' y : Ens, EQ x x' -> P x y -> P x' y) -> (forall E : Ens, EXType _ (P E)) -> forall E : Ens, EXType _ (fun A : Ens => forall x : Ens, IN x E -> EXType _ (fun y : Ens => IN y A /\ P x y)).
Definition choice := forall (A B : Type) (P : A -> B -> Prop), (forall a : A, EXType _ (fun b : B => P a b)) -> EXType _ (fun f : A -> B => forall a : A, P a (f a)).
Definition functional (P : Ens -> Ens -> Prop) := forall x y y' : Ens, P x y -> P x y' -> EQ y y'.
Definition replacement := forall P : Ens -> Ens -> Prop, functional P -> (forall x y y' : Ens, EQ y y' -> P x y -> P x y') -> (forall x x' y : Ens, EQ x x' -> P x y -> P x' y) -> forall X : Ens, EXType _ (fun Y : Ens => forall y : Ens, (IN y Y -> EXType _ (fun x : Ens => IN x X /\ P x y)) /\ (EXType _ (fun x : Ens => IN x X /\ P x y) -> IN y Y)).
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
Inductive Ens' : Type := sup' : forall A : Type, (A -> Ens') -> Ens'.
Inductive EXType' (P : Type) (Q : P -> Prop) : Prop := EXTypei' : forall x : P, Q x -> EXType' P Q.
Inductive prod_t' (A B : Type) : Type := pair_t' : A -> B -> prod_t' A B.
Inductive depprod'' (A : Type) (P : A -> Type) : Type := dep_i'' : forall x : A, P x -> depprod'' A P.
Definition EQ' : Ens' -> Ens' -> Prop.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
apply and.
exact (forall x : A, EXType' _ (fun y : B => eq1 x (g y))).
exact (forall y : B, EXType' _ (fun x : A => eq1 x (g y))).
Defined.
Definition inj : Ens' -> Ens.
simple induction 1; intros A f fr.
exact (sup A fr).
Defined.
Definition Power' (E : Ens') : Ens' := match E with | sup' A f => sup' _ (fun P : A -> Prop => sup' _ (fun c : depprod'' A (fun a : A => P a) => match c with | dep_i'' a p => f a end)) end.
Definition Big := sup Ens' inj.

Theorem IN_Succ : forall E : Ens, IN E (Succ E).
Admitted.

Theorem INC_Succ : forall E : Ens, INC E (Succ E).
unfold INC in |- *; unfold Succ in |- *.
intros.
Admitted.

Theorem IN_Succ_or : forall E E' : Ens, IN E' (Succ E) -> EQ E E' \/ IN E' E.
intros E E' i.
unfold Succ in i.
elim (Union_IN (Paire E (Sing E)) E' i).
intros E1; simple induction 1; intros i1 i2.
elim (Paire_IN E (Sing E) E1 i1).
intros; right; apply IN_sound_right with E1; auto with zfc.
intros; left; cut (IN E' (Sing E)).
auto with zfc.
Admitted.

Theorem E_not_IN_E : forall E : Ens, IN E E -> F.
simple induction E; intros A f r i.
cut False.
simple induction 1.
elim (IN_EXType (sup A f) (sup A f) i); intros a e.
simpl in a.
change (EQ (sup A f) (f a)) in e.
elim (r a).
apply IN_sound_right with (sup A f); auto with zfc.
Admitted.

Theorem Nat_IN_Omega : forall n : nat, IN (Nat n) Omega.
Admitted.

Theorem IN_Omega_EXType : forall E : Ens, IN E Omega -> EXType _ (fun n : nat => EQ (Nat n) E).
simpl in |- *; simple induction 1.
intros n e.
Admitted.

Theorem IN_Nat_EXType : forall (n : nat) (E : Ens), IN E (Nat n) -> EXType _ (fun p : nat => EQ E (Nat p)).
simple induction n.
simpl in |- *.
simple induction 1.
simple induction x.
intros.
change (IN E (Succ (Nat n0))) in H0.
elim (IN_Succ_or (Nat n0) E H0).
intros; exists n0.
auto with zfc.
intros.
Admitted.

Theorem Omega_EQ_Union : EQ Omega (Union Omega).
apply INC_EQ; unfold INC in |- *.
intros.
elim (IN_Omega_EXType E H); intros n e.
apply IN_Union with (Nat (S n)).
auto with zfc.
apply IN_sound_left with (Nat n).
auto with zfc; try auto with zfc.
change (IN (Nat n) (Succ (Nat n))) in |- *; auto with zfc.
intros.
elim (Union_IN Omega E H).
intros e h.
elim h.
intros i1 i2.
elim (IN_Omega_EXType e i1).
intros n e1.
cut (IN E (Nat n)).
intros.
elim (IN_Nat_EXType n E H0); intros.
apply IN_sound_left with (Nat x); auto with zfc.
Admitted.

Theorem Omega_Ord : Ord Omega.
apply Eo with (Union Omega).
apply Lo.
intros.
elim (IN_Omega_EXType e H).
intros n ee.
apply Eo with (Nat n); auto with zfc.
elim n.
auto with zfc.
auto with zfc.
intros.
change (Ord (Succ (Nat n0))) in |- *; auto with zfc.
apply EQ_sym; auto with zfc.
Admitted.

Definition Alpha : Ens -> Ens.
simple induction 1; intros A f r.
apply Union.
apply (sup A).
intros a.
Admitted.

Theorem Choice_Collection : choice -> collection.
unfold collection in |- *; intro; intros P comp G E.
cut (EXType _ (fun f : Ens -> Ens => forall B : Ens, P B (f B))).
simple induction 1; intros f pf.
elim E; intros A g hr; intros.
exists (sup A (fun a : A => f (g a))).
simpl in |- *; intros X i.
elim i; intros a ea.
exists (f (g a)).
split.
exists a; auto with zfc.
apply comp with (g a); auto with zfc.
unfold choice in H.
apply H; intros.
Admitted.

Theorem classical_Collection_Replacement : (forall S : Prop, S \/ (S -> False)) -> collection -> replacement.
unfold replacement in |- *; intros EM Collection P fp comp_r comp_l X.
cut (EXType _ (fun Y : Ens => forall y : Ens, EXType _ (fun x : Ens => IN x X /\ P x y) -> IN y Y)).
simple induction 1; intros Y HY.
exists (Comp Y (fun y : Ens => EXType _ (fun x : Ens => IN x X /\ P x y))).
intros y; split.
intros HC.
apply (IN_Comp_P Y y (fun y0 : Ens => EXType Ens (fun x : Ens => IN x X /\ P x y0))); auto with zfc.
intros w1 w2; simple induction 1; intros x; simple induction 1; intros Ix Px e.
exists x; split; auto with zfc.
apply comp_r with w1; auto with zfc.
intros He.
apply IN_P_Comp.
intros w1 w2; simple induction 1; intros x; simple induction 1; intros Ix Px e.
exists x; split; auto with zfc.
apply comp_r with w1; auto with zfc.
apply HY; auto with zfc.
auto with zfc.
elim (Collection (fun x y : Ens => P x y \/ (forall y' : Ens, P x y' -> False) /\ EQ y Vide)) with X.
intros Y HY.
elim (EM (EXType _ (fun x : Ens => IN x X /\ P x Vide))).
intros Hvide; elim Hvide; intros xv Hxv; exists Y.
intros y; simple induction 1; intros x; simple induction 1; intros Hx1 Hx2.
elim (HY x Hx1).
intros y'; simple induction 1; intros Hy'1 Hy'2.
elim Hy'2.
intros Hy'3; apply IN_sound_left with y'; auto with zfc.
apply fp with x; auto with zfc.
simple induction 1; intros Hy'3 Hy'4.
elim (Hy'3 y Hx2).
intros HP; exists (Comp Y (fun y : Ens => EQ y Vide -> False)).
intros y; simple induction 1; intros x; simple induction 1; intros Hx1 Hx2.
apply IN_P_Comp.
intros w1 w2 Hw1 Hw Hw2; apply Hw1; apply EQ_tran with w2; auto with zfc.
elim (HY x).
intros y'; simple induction 1; intros Hy'1 Hy'2.
elim Hy'2; intros Hy'3.
apply IN_sound_left with y'; auto with zfc.
apply fp with x; auto with zfc.
elim Hy'3; intros Hy'4 Hy'5.
elim (Hy'4 y); auto with zfc.
assumption.
intros e; apply HP; exists x; split; auto with zfc; apply comp_r with y; auto with zfc; apply fp; auto with zfc.
intros x x' y e Hx; elim Hx; intros Hx1.
left; apply comp_l with x; auto with zfc.
right; elim Hx1; intros Hx2 Hx3; split.
2: assumption.
intros y' Hy'; apply (Hx2 y'); apply comp_l with x'; auto with zfc.
intros x; elim (EM (EXType _ (fun y : Ens => P x y))); intros Hx.
elim Hx; intros x0 Hx0; exists x0; left; assumption.
exists Vide; right; split; auto with zfc.
Admitted.

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

Theorem EQC_sym : forall E1 E2 : Ens, EQC E1 E2 -> EQC E2 E1.
simple induction E1; simple induction E2; simpl in |- *; intros.
elim X1; intros; split; intros.
elim (b x); intros.
exists x0; auto with zfc.
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
Admitted.

Theorem CIN_sound_left : forall E E' E'' : Ens, EQC E E' -> CIN E E'' -> CIN E' E''.
simple induction E''; simpl in |- *; intros.
elim X1; intros y p; exists y.
apply EQC_tran with E; auto with zfc.
