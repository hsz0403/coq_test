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

Lemma Ord_trans : forall E : Ens, Ord E -> forall E' : Ens, IN E' E -> INC E' E.
simple induction E; intros A f HR o E' i.
unfold INC in |- *.
intros E'' i'.
apply plump with E'.
auto with zfc.
apply IN_Ord_Ord with (sup A f); auto with zfc.
apply IN_Ord_Ord with E'; auto with zfc; apply IN_Ord_Ord with (sup A f); auto with zfc.
auto with zfc.
elim i; intros a e.
apply INC_sound_right with (f a); auto with zfc.
apply HR; auto with zfc.
apply IN_Ord_Ord with (sup A f); auto with zfc; exists a; auto with zfc.
apply IN_sound_right with E'; auto with zfc.
