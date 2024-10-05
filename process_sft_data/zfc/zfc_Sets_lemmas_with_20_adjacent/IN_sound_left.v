Global Set Asymmetric Patterns.
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

Definition EQ : Ens -> Ens -> Prop.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
apply and.
exact (forall x : A, EXType _ (fun y : B => eq1 x (g y))).
Admitted.

Definition INC : Ens -> Ens -> Prop.
intros E1 E2.
Admitted.

Theorem EQ_refl : forall E : Ens, EQ E E.
simple induction E.
intros A f HR.
simpl in |- *.
split; intros.
exists x; auto.
Admitted.

Theorem EQ_tran : forall E1 E2 E3 : Ens, EQ E1 E2 -> EQ E2 E3 -> EQ E1 E3.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2; simple induction E3; intros A3 f3 r3; simpl in |- *; intros e1 e2.
split; (elim e1; intros I1 I2; elim e2; intros I3 I4).
intros a1; elim (I1 a1); intros a2.
elim (I3 a2); intros a3.
exists a3.
apply r1 with (f2 a2); auto.
intros a3; elim (I4 a3); intros a2; elim (I2 a2); intros a1; exists a1.
Admitted.

Theorem EQ_sym : forall E1 E2 : Ens, EQ E1 E2 -> EQ E2 E1.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2; simpl in |- *; simple induction 1; intros e1 e2; split.
intros a2; elim (e2 a2); intros a1 H1; exists a1; auto.
Admitted.

Theorem EQ_INC : forall E E' : Ens, EQ E E' -> INC E E'.
simple induction E; intros A f r; simple induction E'; intros A' f' r'; simpl in |- *; simple induction 1; intros e1 e2; unfold INC in |- *; simpl in |- *.
intros C; simple induction 1; intros a ea; elim (e1 a); intros a' ea'; exists a'.
Admitted.

Theorem INC_EQ : forall E E' : Ens, INC E E' -> INC E' E -> EQ E E'.
simple induction E; intros A f r; simple induction E'; intros A' f' r'; unfold INC in |- *; simpl in |- *; intros I1 I2; split.
intros a; apply I1.
exists a; auto with zfc.
intros a'; cut (EXType A (fun x : A => EQ (f' a') (f x))).
simple induction 1; intros a ea; exists a; auto with zfc.
Admitted.

Theorem IN_sound_right : forall E E' E'' : Ens, EQ E' E'' -> IN E E' -> IN E E''.
Admitted.

Theorem INC_refl : forall E : Ens, INC E E.
Admitted.

Theorem INC_tran : forall E E' E'' : Ens, INC E E' -> INC E' E'' -> INC E E''.
Admitted.

Theorem INC_sound_left : forall E E' E'' : Ens, EQ E E' -> INC E E'' -> INC E' E''.
simple induction E''; unfold INC in |- *; simpl in |- *; intros A f HR e H1 E0 i; apply H1.
Admitted.

Theorem INC_sound_right : forall E E' E'' : Ens, EQ E' E'' -> INC E E' -> INC E E''.
simple induction E'; simple induction E''; unfold INC in |- *; simpl in |- *; intros.
elim (H2 E0); try assumption; intros.
elim H1; intros HA HB; elim (HA x); intros.
Admitted.

Theorem IN_sound_left : forall E E' E'' : Ens, EQ E E' -> IN E E'' -> IN E' E''.
simple induction E''; intros A'' f'' r'' e; simpl in |- *; simple induction 1; intros a'' p; exists a''; apply EQ_tran with E; auto with zfc.
