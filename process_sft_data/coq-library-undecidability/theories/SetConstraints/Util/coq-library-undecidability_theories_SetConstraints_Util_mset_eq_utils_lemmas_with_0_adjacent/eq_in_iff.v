Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC Undecidability.SetConstraints.Util.Facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Arguments mset_eq !A !B.
Ltac eq_trivial := move=> ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil, eta_reduction); unlock; by lia.

Lemma eq_in_iff {A B} : A ≡ B -> forall c, In c A <-> In c B.
Proof.
rewrite /mset_eq => H c.
constructor=> Hc.
-
have := iffLR (count_occ_In Nat.eq_dec A c) Hc.
move: (H c) => ->.
by move /(count_occ_In Nat.eq_dec B c).
-
have := iffLR (count_occ_In Nat.eq_dec B c) Hc.
move: (H c) => <-.
by move /(count_occ_In Nat.eq_dec A c).
