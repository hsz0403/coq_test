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

Lemma plump : forall E : Ens, Ord E -> forall E1 E2 : Ens, Ord E1 -> Ord E2 -> IN E1 E -> INC E2 E1 -> IN E2 E.
simple induction E; intros A f HR.
simple induction 1; intros o1 o2.
intros E1 E2 o11 o22 i inc.
elim (IN_EXType _ _ i).
intros a eq; simpl in a; simpl in eq.
cut (INC E2 (f a)).
intros inc0; apply (o2 a) with (p := inc0).
exists a; auto with zfc.
apply ord_tech with (E1 := E2) (p1 := INC_refl E2) (p2 := inc0).
assumption.
apply INC_sound_right with E1; auto with zfc.
