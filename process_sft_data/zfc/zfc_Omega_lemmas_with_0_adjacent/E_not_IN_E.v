Require Import Sets.
Require Import Axioms.
Definition Class_succ (E : Ens) := Union (Paire E (Sing E)).
Definition Nat : nat -> Ens.
simple induction 1; intros.
exact Vide.
exact (Class_succ X).
Defined.
Definition Omega : Ens := sup nat Nat.
Hint Resolve IN_Class_succ INC_Class_succ: zfc.
Hint Resolve Nat_IN_Omega: zfc.
Fixpoint Vee (E : Ens) : Ens := match E with | sup A f => Union (sup A (fun a : A => Power (Vee (f a)))) end.

Theorem E_not_IN_E : forall E : Ens, IN E E -> F.
simple induction E; intros A f r i.
cut False.
simple induction 1.
elim (IN_EXType (sup A f) (sup A f) i); intros a e.
simpl in a.
change (EQ (sup A f) (f a)) in e.
elim (r a).
apply IN_sound_right with (sup A f); auto with zfc.
exists a; auto with zfc.
