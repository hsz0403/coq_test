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

Lemma Ord_intro : forall E : Ens, (forall E' : Ens, IN E' E -> Ord E') -> (forall E1 E2 : Ens, Ord E1 -> Ord E2 -> IN E1 E -> INC E2 E1 -> IN E2 E) -> Ord E.
simple induction E; intros A f HR h1 h2; split.
intros a i.
change (Ord (f a)) in |- *; apply h1; exists a; auto with zfc.
intros a E1 i inc o.
apply h2 with (E1 := f a).
auto with zfc.
auto with zfc.
unfold Ord in |- *.
apply (ord_tech (f a)) with (p1 := inc) (p2 := INC_refl E1); auto with zfc.
exists a; auto with zfc.
auto with zfc.
