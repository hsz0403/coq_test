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

Lemma Ord_Succ : forall E : Ens, Ord E -> Ord (Succ E).
unfold Succ in |- *; intros E o.
apply Ord_intro.
intros.
apply IN_Comp_P with (Power E).
intros w1 w2 o1 e; apply Ord_sound with w1; auto with zfc.
auto with zfc.
intros E1 E2 o1 o2 i inc.
apply IN_P_Comp; auto with zfc.
intros w1 w2 ow1 e; apply Ord_sound with w1; auto with zfc.
apply INC_IN_Power.
apply INC_tran with E1; auto with zfc.
cut (IN E1 (Power E)).
intros i1.
apply IN_Power_INC; try trivial with zfc.
cut (INC (Comp (Power E) Ord) (Power E)).
intros inc1.
apply inc1; try trivial with zfc.
apply Comp_INC; try trivial with zfc.
