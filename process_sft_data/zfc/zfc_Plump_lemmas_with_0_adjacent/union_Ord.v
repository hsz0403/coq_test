Require Export Sets.
Require Export Axioms.
Require Export Omega.
Definition ord : forall E E' : Ens, INC E' E -> Prop.
simple induction E.
intros A f HR.
intros E' i.
apply and.
exact (forall a : A, IN (f a) E' -> HR a (f a) (INC_refl (f a))).
exact (forall (a : A) (e : Ens), IN (f a) E' -> forall p : INC e (f a), HR a e p -> IN e E').
Defined.
Definition Ord (E : Ens) := ord E E (INC_refl E).
Definition Succ (E : Ens) := Comp (Power E) Ord.
Definition PI1 : forall (A : Type) (P : A -> Type), depprod A P -> A.
simple induction 1; intros a p.
exact a.
Defined.
Definition PI2 : forall (A : Type) (P : A -> Type) (c : depprod A P), P (PI1 A P c).
simple induction c.
intros a p.
exact p.
Defined.

Lemma Union_Ord : forall E : Ens, (forall E' : Ens, IN E' E -> Ord E') -> Ord (Union E).
simple induction E; intros A f HR h.
apply Ord_intro.
intros E' i.
elim i.
simple induction x; intros a.
intros b e.
simpl in e.
apply Ord_sound with (pi2 (f a) b).
auto with zfc.
apply IN_Ord_Ord with (f a); auto with zfc.
apply h; exists a; auto with zfc.
generalize b; elim (f a); simpl in |- *.
intros.
exists b0; auto with zfc.
intros.
elim (Union_IN (sup A f) E1); auto with zfc.
intros E3.
simple induction 1.
intros i1 i2.
apply IN_Union with E3.
auto with zfc.
apply plump with E1; auto with zfc.
