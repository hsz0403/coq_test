Require Import List.
Inductive term : Set := | atom : nat -> term | arr : term -> term -> term.
Definition valuation : Set := nat -> term.
Fixpoint substitute (f: valuation) (t: term) : term := match t with | atom n => f n | arr s t => arr (substitute f s) (substitute f t) end.
Definition constraint : Set := ((bool * nat) * (nat * bool)).
Definition models (φ ψ0 ψ1: valuation) : constraint -> Prop := fun '((a, x), (y, b)) => match φ y with | atom _ => False | arr s t => (if b then t else s) = substitute (if a then ψ1 else ψ0) (φ x) end.
Definition SSemiU (p : list constraint) := exists (φ ψ0 ψ1: valuation), forall (c : constraint), In c p -> models φ ψ0 ψ1 c.
Definition inequality : Set := (term * term).
Definition solution (φ : valuation) : inequality -> Prop := fun '(s, t) => exists (ψ : valuation), substitute ψ (substitute φ s) = substitute φ t.
Definition SemiU (p: list inequality) := exists (φ: valuation), forall (c: inequality), In c p -> solution φ c.
Definition RU2SemiU : term * term * term -> Prop := fun '(s0, s1, t) => exists (φ ψ0 ψ1: valuation), substitute ψ0 (substitute φ s0) = substitute φ t /\ substitute ψ1 (substitute φ s1) = substitute φ t.
Definition LU2SemiU : term * term * term -> Prop := fun '(s, t0, t1) => exists (φ ψ0 ψ1: valuation), substitute ψ0 (substitute φ s) = substitute φ t0 /\ substitute ψ1 (substitute φ s) = substitute φ t1.