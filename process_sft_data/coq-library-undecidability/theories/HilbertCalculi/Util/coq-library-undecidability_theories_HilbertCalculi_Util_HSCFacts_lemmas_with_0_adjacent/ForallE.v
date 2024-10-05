Require Import List Lia.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Require Import Undecidability.HilbertCalculi.HSC.
Set Default Goal Selector "!".
Fixpoint size s := match s with | var _ => 1 | arr s t => S (size s + size t) end.
Fixpoint arguments (k: nat) (t: formula) := match k with | 0 => [] | S k => match t with | var _ => [] | arr s t => s :: (arguments k t) end end.
Fixpoint target (k: nat) (t: formula) := match k with | 0 => t | S k => match t with | var _ => t | arr _ t => target k t end end.
Inductive der (Gamma: list formula) : nat -> formula -> Prop := | der_var {ζ: nat -> formula} {s t: formula} {k n: nat} : In s Gamma -> Forall (der Gamma n) (arguments k (substitute ζ s)) -> target k (substitute ζ s) = t -> der Gamma (S n) t.

Lemma ForallE {T : Type} {P : T -> Prop} {l} : Forall P l -> if l is x :: l then P x /\ Forall P l else True.
Proof.
by case.
