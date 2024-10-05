Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC Undecidability.SetConstraints.Util.Facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Arguments mset_eq !A !B.
Ltac eq_trivial := move=> ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil, eta_reduction); unlock; by lia.

Lemma eq_mapI {A B} : A ≡ B -> map S A ≡ map S B.
Proof.
rewrite /mset_eq => + c.
move=> /(_ (Nat.pred c)).
case: c.
{
move=> _.
have H := iffLR (count_occ_not_In _ _ _).
rewrite ? {}H; last done.
all: by rewrite in_map_iff=> [[? [? ?]]].
}
move=> c.
rewrite - ? (count_occ_map S Nat.eq_dec Nat.eq_dec); last done.
all: move=> >; by case.
