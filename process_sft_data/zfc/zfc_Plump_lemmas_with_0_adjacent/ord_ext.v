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

Lemma ord_ext : forall (E E' E'' : Ens) (p' : INC E' E) (p'' : INC E'' E), EQ E' E'' -> ord E E' p' -> ord E E'' p''.
simple induction E.
intros A f HR.
simpl in |- *.
intros E' E'' I' I'' e.
simple induction 1.
intros o1 o2.
clear H.
split.
auto with zfc.
intros; apply o1.
apply IN_sound_right with E''; auto with zfc.
intros.
apply IN_sound_right with E'; auto with zfc.
apply (o2 a) with (p := p).
apply IN_sound_right with E''; auto with zfc.
auto with zfc.
