Require Import List Lia.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Require Import Undecidability.HilbertCalculi.HSC.
Set Default Goal Selector "!".
Fixpoint size s := match s with | var _ => 1 | arr s t => S (size s + size t) end.
Fixpoint arguments (k: nat) (t: formula) := match k with | 0 => [] | S k => match t with | var _ => [] | arr s t => s :: (arguments k t) end end.
Fixpoint target (k: nat) (t: formula) := match k with | 0 => t | S k => match t with | var _ => t | arr _ t => target k t end end.
Inductive der (Gamma: list formula) : nat -> formula -> Prop := | der_var {ζ: nat -> formula} {s t: formula} {k n: nat} : In s Gamma -> Forall (der Gamma n) (arguments k (substitute ζ s)) -> target k (substitute ζ s) = t -> der Gamma (S n) t.

Lemma hsc_der {Gamma t} : hsc Gamma t -> exists n, der Gamma n t.
Proof.
elim.
-
move=> ζ s /der_var => /(_ ζ (substitute ζ s) 0 0).
move /(_ ltac:(by constructor)).
move /(_ ltac:(done)).
move=> ?.
by exists 1.
-
move=> s' t' _ [n1 /derE +] _ [n2 /derE].
move=> [ζ1 [s1 [k1 [-> [Hs1 [? Hk1]]]]]].
move=> [ζ2 [s2 [k2 [-> [? [? ?]]]]]].
exists (S (S (n1+n2))).
apply: (der_var _ (ζ := ζ1) (s := s1) (k := S k1)).
+
done.
+
rewrite (arguments_S ltac:(eassumption)).
apply /Forall_app.
constructor.
*
apply: Forall_impl; last eassumption.
move=> ? /der_mon.
apply.
by lia.
*
constructor; last done.
apply: der_var; last eassumption; first done.
apply: Forall_impl; last eassumption.
move=> ? /der_mon.
apply.
by lia.
+
apply: target_S.
by eassumption.
