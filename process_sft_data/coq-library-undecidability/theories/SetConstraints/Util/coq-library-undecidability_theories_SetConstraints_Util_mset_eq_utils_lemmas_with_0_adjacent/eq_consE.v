Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC Undecidability.SetConstraints.Util.Facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Arguments mset_eq !A !B.
Ltac eq_trivial := move=> ?; rewrite ? (count_occ_app, count_occ_cons, count_occ_nil, eta_reduction); unlock; by lia.

Lemma eq_consE {a A B}: a :: A ≡ B -> exists B1 B2, B = B1 ++ (a :: B2) /\ A ≡ (B1 ++ B2).
Proof.
move=> /copy [/mset_eq_utils.eq_in_iff /(_ a) /iffLR /(_ ltac:(by left))].
move /(@in_split _ _) => [B1 [B2 ->]].
under (mset_eq_utils.eq_lr mset_eq_utils.eq_refl (B' := a :: (B1 ++ B2))).
{
by mset_eq_utils.eq_trivial.
}
move /mset_eq_utils.eq_consP => H.
exists B1, B2.
by constructor.
