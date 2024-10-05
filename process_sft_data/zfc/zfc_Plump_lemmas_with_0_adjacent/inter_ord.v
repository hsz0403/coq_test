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

Lemma Inter_Ord : forall E : Ens, (forall E' : Ens, IN E' E -> Ord E') -> Ord (Inter E).
simple induction E; intros A f HR H.
apply Ord_intro.
intros E' i.
elim i.
simple induction x.
intro a; simple induction p.
intros b h.
intros e.
apply IN_Ord_Ord with (f a).
apply H; exists a; auto with zfc.
apply IN_sound_left with (pi2 (f a) b); auto with zfc.
intros E1 E2 o1 o2 i inc.
elim i.
simple induction x.
intro a; simple induction p.
intros b h e.
apply all_IN_Inter with (f a).
exists a; auto with zfc.
intros.
apply plump with E1; auto with zfc.
apply IN_Inter_all with (sup A f); auto with zfc.
