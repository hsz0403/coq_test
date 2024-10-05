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

Theorem Nat_IN_Omega : forall n : nat, IN (Nat n) Omega.
intros; simpl in |- *; exists n; auto with zfc.
