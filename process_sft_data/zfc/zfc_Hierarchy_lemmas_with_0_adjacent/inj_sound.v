Require Import Sets.
Require Import Axioms.
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

Theorem inj_sound : forall E1 E2 : Ens', EQ' E1 E2 -> EQ (inj E1) (inj E2).
simple induction E1; intros A1 f1 fr1; simple induction E2; intros A2 f2 r2; simpl in |- *.
simple induction 1; intros HR1 HR2; split.
intros a1; elim (HR1 a1); intros a2 Ha2; exists a2; auto with zfc.
intros a2; elim (HR2 a2); intros a1 Ha1; exists a1; auto with zfc.
