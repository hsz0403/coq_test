Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC Undecidability.SetConstraints.Util.Facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Arguments mset_eq !A !B.
Ltac eq_trivial := move=> ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil, eta_reduction); unlock; by lia.

Lemma eq_mapE {A f} : (forall n, n < f n) -> map f A ≡ A -> A = [].
Proof.
case (nil_or_ex_max A); first done.
move=> [a [Ha /Forall_forall HA]] Hf /eq_in_iff /(_ (f a)) /iffLR.
rewrite in_map_iff.
apply: unnest; first by exists a.
move /HA.
move: (Hf a).
by lia.
