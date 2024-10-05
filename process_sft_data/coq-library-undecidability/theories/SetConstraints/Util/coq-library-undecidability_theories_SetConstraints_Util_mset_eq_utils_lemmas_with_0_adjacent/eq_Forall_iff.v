Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC Undecidability.SetConstraints.Util.Facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Arguments mset_eq !A !B.
Ltac eq_trivial := move=> ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil, eta_reduction); unlock; by lia.

Lemma eq_Forall_iff {A B} : A ≡ B -> forall P, (Forall P A <-> Forall P B).
Proof.
move /eq_in_iff => H P.
rewrite ? Forall_forall.
constructor; by firstorder done.
