Require Import List Lia.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Require Import Undecidability.HilbertCalculi.HSC.
Set Default Goal Selector "!".
Fixpoint size s := match s with | var _ => 1 | arr s t => S (size s + size t) end.
Fixpoint arguments (k: nat) (t: formula) := match k with | 0 => [] | S k => match t with | var _ => [] | arr s t => s :: (arguments k t) end end.
Fixpoint target (k: nat) (t: formula) := match k with | 0 => t | S k => match t with | var _ => t | arr _ t => target k t end end.
Inductive der (Gamma: list formula) : nat -> formula -> Prop := | der_var {ζ: nat -> formula} {s t: formula} {k n: nat} : In s Gamma -> Forall (der Gamma n) (arguments k (substitute ζ s)) -> target k (substitute ζ s) = t -> der Gamma (S n) t.

Lemma der_mon {n m t Gamma} : der Gamma n t -> n <= m -> der Gamma m t.
Proof.
elim: n m Gamma t; first by move=> > /der_0E.
move=> n IH m Gamma t.
move /derE => [ζ [s' [k']]].
move=> [_ [? [? ?]]] ?.
have -> : m = S (Nat.pred m) by lia.
apply: der_var; try eassumption.
apply: Forall_impl; last by eassumption.
move=> ? /IH.
apply.
by lia.
