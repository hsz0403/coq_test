Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC Undecidability.SetConstraints.Util.Facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Arguments mset_eq !A !B.
Ltac eq_trivial := move=> ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil, eta_reduction); unlock; by lia.

Lemma eq_repeatE {a A n} : repeat a n ≡ A -> A = repeat a n.
Proof.
move=> /copy [/eq_length].
rewrite repeat_length => HlA.
move /eq_Forall_iff /(_ (fun c => a = c)) /iffLR.
apply: unnest.
{
clear.
elim: n; firstorder (by constructor).
}
subst n.
elim: A; first done.
move=> b A IH /Forall_cons_iff [<-] /IH -> /=.
by rewrite repeat_length.
