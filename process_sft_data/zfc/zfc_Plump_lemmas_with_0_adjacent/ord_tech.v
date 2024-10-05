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

Lemma ord_tech : forall (E1 E2 E : Ens) (p1 : INC E E1) (p2 : INC E E2), ord E1 E p1 -> ord E2 E p2.
simple induction E1; intros A1 f1 HR1; simple induction E2; intros A2 f2 HR2 E p1 p2.
simple induction 1; intros o1 o2.
split.
intros a2 i2.
elim (IN_EXType _ _ i2).
intros x e.
change (Ord (f2 a2)) in |- *.
apply Ord_sound with (pi2 E x).
auto with zfc.
cut (IN (pi2 E x) (sup A1 f1)).
simple induction 1; intros a1 e1.
apply Ord_sound with (f1 a1); auto with zfc.
unfold Ord in |- *; apply o1.
apply IN_sound_left with (pi2 E x); auto with zfc.
apply IN_sound_left with (f2 a2); auto with zfc.
unfold INC in p1; apply p1; auto with zfc.
apply IN_sound_left with (f2 a2); auto with zfc.
intros a2 e i inc o.
elim (IN_EXType _ _ i).
intros x e2.
cut (IN (pi2 E x) (sup A1 f1)).
simple induction 1; intros a1 e1.
cut (INC e (f1 a1)).
intros inc1.
apply (o2 a1) with (p := inc1).
apply IN_sound_left with (pi2 E x).
auto with zfc.
apply IN_sound_left with (f2 a2); auto with zfc.
elim (ord_sound (f1 a1) (f2 a2)) with (p := inc1) (p' := inc).
intros h1 h2.
auto with zfc.
apply EQ_tran with (pi2 E x).
auto with zfc.
auto with zfc.
auto with zfc.
apply INC_sound_right with (pi2 E x).
auto with zfc.
apply INC_sound_right with (f2 a2); auto with zfc.
apply IN_sound_left with (f2 a2); auto with zfc.
