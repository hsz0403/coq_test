Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC Undecidability.SetConstraints.Util.Facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Arguments mset_eq !A !B.
Ltac eq_trivial := move=> ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil, eta_reduction); unlock; by lia.

Lemma eq_eq {A B}: A = B -> A ≡ B.
Proof.
Admitted.

Lemma eq_symm {A B} : A ≡ B -> B ≡ A.
Proof.
Admitted.

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
Admitted.

Lemma eq_nilE {A} : [] ≡ A -> A = [].
Proof.
case: A; first done.
move=> a A /eq_in_iff /(_ a) /iffRL.
Admitted.

Lemma eq_trans {A B C} : A ≡ B -> B ≡ C -> A ≡ C.
Proof.
rewrite /mset_eq => + + c.
move=> /(_ c) + /(_ c).
Admitted.

Lemma eq_Forall_iff {A B} : A ≡ B -> forall P, (Forall P A <-> Forall P B).
Proof.
move /eq_in_iff => H P.
rewrite ? Forall_forall.
Admitted.

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
Admitted.

Lemma eq_appI {A B A' B'} : A ≡ A' -> B ≡ B' -> A ++ B ≡ A' ++ B'.
Proof.
rewrite /mset_eq => + + c.
move=> /(_ c) + /(_ c).
rewrite ? count_occ_app.
Admitted.

Lemma eq_cons_iff {a A B} : (a :: A) ≡ (a :: B) <-> A ≡ B.
Proof.
rewrite /mset_eq.
constructor=> + c => /(_ c).
Admitted.

Lemma eq_app_iff {A B C} : (A ++ B) ≡ (A ++ C) <-> B ≡ C.
Proof.
elim: A; first done.
move=> a A IH /=.
Admitted.

Lemma eq_refl {A} : A ≡ A.
Proof.
done.
