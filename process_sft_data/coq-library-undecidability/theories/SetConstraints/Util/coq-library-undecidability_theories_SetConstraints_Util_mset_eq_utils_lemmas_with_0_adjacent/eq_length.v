Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC Undecidability.SetConstraints.Util.Facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Arguments mset_eq !A !B.
Ltac eq_trivial := move=> ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil, eta_reduction); unlock; by lia.

Lemma eq_length {A B} : A ≡ B -> length A = length B.
elim /(measure_ind (@length nat)) : A B.
case.
{
by move=> _ B /eq_nilE ->.
}
move=> a A IH B /copy [/eq_in_iff /(_ a) /iffLR].
apply: unnest; first by left.
move /(@in_split _ _) => [B1 [B2 ->]].
under (eq_lr eq_refl (B' := a :: (B1 ++ B2))).
{
by eq_trivial.
}
move /eq_cons_iff.
move /IH.
apply: unnest; first done.
rewrite ? app_length => /=.
by lia.
