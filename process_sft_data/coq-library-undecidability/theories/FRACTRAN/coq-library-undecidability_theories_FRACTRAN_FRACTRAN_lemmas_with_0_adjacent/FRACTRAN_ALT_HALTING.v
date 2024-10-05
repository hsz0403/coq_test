Require Import List Arith.
From Undecidability.Shared.Libs.DLW Require Import gcd rel_iter pos vec.
From Undecidability.FRACTRAN.Utils Require Import prime_seq.
Reserved Notation "l '/F/' x → y" (at level 70, no associativity).
Implicit Type l : list (nat*nat).
Inductive fractran_step : list (nat*nat) -> nat -> nat -> Prop := | in_fractran_0 : forall p q l x y, q*y = p*x -> (p,q)::l /F/ x → y | in_fractran_1 : forall p q l x y, ~ divides q (p*x) -> l /F/ x → y -> (p,q)::l /F/ x → y where "l /F/ x → y" := (fractran_step l x y).
Definition fractran_stop l x := forall z, ~ l /F/ x → z.
Definition fractran_steps l := rel_iter (fractran_step l).
Definition fractran_compute l x y := exists n, fractran_steps l n x y.
Definition fractran_terminates l x := exists y, fractran_compute l x y /\ fractran_stop l y.
Notation "l '/F/' x ↓ " := (fractran_terminates l x) (at level 70, no associativity).
Definition FRACTRAN_PROBLEM := (list (nat*nat) * nat)%type.
Definition FRACTRAN_HALTING (P : FRACTRAN_PROBLEM) := let (l,x) := P in l /F/ x ↓.
Definition fractran_regular l := Forall (fun c => snd c <> 0) l.
Definition FRACTRAN_REG_PROBLEM := { l : list (nat*nat) & { _ : nat | fractran_regular l } }.
Definition FRACTRAN_REG_HALTING (P : FRACTRAN_REG_PROBLEM) : Prop.
Proof.
destruct P as (l & x & _).
exact (l /F/ x ↓).
Defined.
Definition FRACTRAN_ALT_PROBLEM := (list (nat*nat) * { n : nat & vec nat n })%type.
Definition FRACTRAN_ALT_HALTING : FRACTRAN_ALT_PROBLEM -> Prop.
Proof.
intros (l & n & v).
exact (l /F/ ps 1 * exp 1 v ↓).
Defined.

Definition FRACTRAN_ALT_HALTING : FRACTRAN_ALT_PROBLEM -> Prop.
Proof.
intros (l & n & v).
exact (l /F/ ps 1 * exp 1 v ↓).
