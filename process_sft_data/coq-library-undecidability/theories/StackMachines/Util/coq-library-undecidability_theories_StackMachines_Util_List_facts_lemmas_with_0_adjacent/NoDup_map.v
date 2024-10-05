Require Import List Lia.
Import ListNotations.
Require Import Undecidability.StackMachines.Util.Nat_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma NoDup_map {X Y: Type} {f : X -> Y} {l : list X} : (forall x1 x2, f x1 = f x2 -> x1 = x2) -> NoDup l -> NoDup (map f l).
Proof.
move=> Hf.
elim: l.
{
move=> ?.
by apply: NoDup_nil.
}
move=> x l IH /NoDup_cons_iff [Hx /IH Hfl] /=.
apply /NoDup_cons_iff.
constructor; last done.
rewrite in_map_iff.
by move=> [x'] [/Hf ->].
