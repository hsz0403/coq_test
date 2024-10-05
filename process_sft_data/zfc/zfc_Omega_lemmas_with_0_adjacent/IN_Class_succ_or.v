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

Theorem IN_Class_succ_or : forall E E' : Ens, IN E' (Class_succ E) -> EQ E E' \/ IN E' E.
intros E E' i.
unfold Class_succ in i.
elim (Union_IN (Paire E (Sing E)) E' i).
intros E1; simple induction 1; intros i1 i2.
elim (Paire_IN E (Sing E) E1 i1).
intros; right; apply IN_sound_right with E1; auto with zfc.
intros; left; cut (IN E' (Sing E)).
auto with zfc.
apply IN_sound_right with E1; auto with zfc.
