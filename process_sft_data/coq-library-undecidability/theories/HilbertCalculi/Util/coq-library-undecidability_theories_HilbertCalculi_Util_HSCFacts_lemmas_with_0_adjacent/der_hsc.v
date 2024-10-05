Require Import List Lia.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Require Import Undecidability.HilbertCalculi.HSC.
Set Default Goal Selector "!".
Fixpoint size s := match s with | var _ => 1 | arr s t => S (size s + size t) end.
Fixpoint arguments (k: nat) (t: formula) := match k with | 0 => [] | S k => match t with | var _ => [] | arr s t => s :: (arguments k t) end end.
Fixpoint target (k: nat) (t: formula) := match k with | 0 => t | S k => match t with | var _ => t | arr _ t => target k t end end.
Inductive der (Gamma: list formula) : nat -> formula -> Prop := | der_var {ζ: nat -> formula} {s t: formula} {k n: nat} : In s Gamma -> Forall (der Gamma n) (arguments k (substitute ζ s)) -> target k (substitute ζ s) = t -> der Gamma (S n) t.

Lemma der_hsc {Gamma t n} : der Gamma n t -> hsc Gamma t.
Proof.
elim: n Gamma t; first by move=> > /der_0E.
move=> n IH Gamma t /derE.
move=> [ζ [s [k [-> [? [+ +]]]]]].
have : hsc Gamma (substitute ζ s) by apply: hsc_var.
move: IH.
clear.
move: (substitute ζ s) => {}s.
clear.
move=> IH.
elim: k s.
{
move=> s /= *.
by subst t.
}
move=> k IHk.
case.
{
move=> ? /= *.
by subst t.
}
move=> s1 s2 /= /hsc_arr + /ForallE [/IH H].
by move=> /(_ H){H} /IHk.
