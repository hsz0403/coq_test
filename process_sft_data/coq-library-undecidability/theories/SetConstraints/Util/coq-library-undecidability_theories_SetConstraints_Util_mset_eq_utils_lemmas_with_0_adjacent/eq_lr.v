Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC Undecidability.SetConstraints.Util.Facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Arguments mset_eq !A !B.
Ltac eq_trivial := move=> ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil, eta_reduction); unlock; by lia.

Lemma eq_lr {A B A' B'}: A ≡ A' -> B ≡ B' -> (A ≡ B) <-> (A' ≡ B').
Proof.
move=> HA HB.
constructor.
-
move /eq_trans.
move /(_ _ HB).
move /(eq_trans _).
by move /(_ _ (eq_symm HA)).
-
move /eq_trans.
move /(_ _ (eq_symm HB)).
move /(eq_trans _).
by move /(_ _ HA).
