Require Import Sets.
Require Import Axioms.
Require Import Cartesian.
Require Import Omega.
Definition collection := forall P : Ens -> Ens -> Prop, (forall x x' y : Ens, EQ x x' -> P x y -> P x' y) -> (forall E : Ens, EXType _ (P E)) -> forall E : Ens, EXType _ (fun A : Ens => forall x : Ens, IN x E -> EXType _ (fun y : Ens => IN y A /\ P x y)).
Definition choice := forall (A B : Type) (P : A -> B -> Prop), (forall a : A, EXType _ (fun b : B => P a b)) -> EXType _ (fun f : A -> B => forall a : A, P a (f a)).
Definition functional (P : Ens -> Ens -> Prop) := forall x y y' : Ens, P x y -> P x y' -> EQ y y'.
Definition replacement := forall P : Ens -> Ens -> Prop, functional P -> (forall x y y' : Ens, EQ y y' -> P x y -> P x y') -> (forall x x' y : Ens, EQ x x' -> P x y -> P x' y) -> forall X : Ens, EXType _ (fun Y : Ens => forall y : Ens, (IN y Y -> EXType _ (fun x : Ens => IN x X /\ P x y)) /\ (EXType _ (fun x : Ens => IN x X /\ P x y) -> IN y Y)).

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
elim (G a); intros b hb; exists b; auto with zfc.
