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

Definition Nat : nat -> Ens.
simple induction 1; intros.
exact Vide.
Admitted.

Theorem IN_Class_succ : forall E : Ens, IN E (Class_succ E).
Admitted.

Theorem INC_Class_succ : forall E : Ens, INC E (Class_succ E).
unfold INC in |- *; unfold Class_succ in |- *.
intros.
Admitted.

Theorem IN_Class_succ_or : forall E E' : Ens, IN E' (Class_succ E) -> EQ E E' \/ IN E' E.
intros E E' i.
unfold Class_succ in i.
elim (Union_IN (Paire E (Sing E)) E' i).
intros E1; simple induction 1; intros i1 i2.
elim (Paire_IN E (Sing E) E1 i1).
intros; right; apply IN_sound_right with E1; auto with zfc.
intros; left; cut (IN E' (Sing E)).
auto with zfc.
Admitted.

Theorem E_not_IN_E : forall E : Ens, IN E E -> F.
simple induction E; intros A f r i.
cut False.
simple induction 1.
elim (IN_EXType (sup A f) (sup A f) i); intros a e.
simpl in a.
change (EQ (sup A f) (f a)) in e.
elim (r a).
apply IN_sound_right with (sup A f); auto with zfc.
Admitted.

Theorem Nat_IN_Omega : forall n : nat, IN (Nat n) Omega.
Admitted.

Theorem IN_Omega_EXType : forall E : Ens, IN E Omega -> EXType _ (fun n : nat => EQ (Nat n) E).
simpl in |- *; simple induction 1.
intros n e.
Admitted.

Theorem Omega_EQ_Union : EQ Omega (Union Omega).
apply INC_EQ; unfold INC in |- *.
intros.
elim (IN_Omega_EXType E H); intros n e.
apply IN_Union with (Nat (S n)).
auto with zfc.
apply IN_sound_left with (Nat n).
auto with zfc; try auto with zfc.
change (IN (Nat n) (Class_succ (Nat n))) in |- *; auto with zfc.
intros.
elim (Union_IN Omega E H).
intros e h.
elim h.
intros i1 i2.
elim (IN_Omega_EXType e i1).
intros n e1.
cut (IN E (Nat n)).
intros.
elim (IN_Nat_EXType n E H0); intros.
apply IN_sound_left with (Nat x); auto with zfc.
Admitted.

Theorem IN_Nat_EXType : forall (n : nat) (E : Ens), IN E (Nat n) -> EXType _ (fun p : nat => EQ E (Nat p)).
simple induction n.
simpl in |- *.
simple induction 1.
simple induction x.
intros.
change (IN E (Class_succ (Nat n0))) in H0.
elim (IN_Class_succ_or (Nat n0) E H0).
intros; exists n0.
auto with zfc.
intros.
elim (H E); auto with zfc.
