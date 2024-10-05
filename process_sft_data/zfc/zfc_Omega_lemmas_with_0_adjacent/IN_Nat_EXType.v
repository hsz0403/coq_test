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
