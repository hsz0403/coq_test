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

Theorem EQ_sym : forall E1 E2 : Ens, EQ E1 E2 -> EQ E2 E1.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2; simpl in |- *; simple induction 1; intros e1 e2; split.
intros a2; elim (e2 a2); intros a1 H1; exists a1; auto.
intros a1; elim (e1 a1); intros a2 H2; exists a2; auto.
