Require Import PeanoNat Lia List.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC.
From Undecidability.SetConstraints.Util Require Import Facts mset_eq_utils.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Definition eval p A := fold_right plus 0 (map (fun n => Nat.pow p n) A).
Definition eval_norm := (@eval_appP, @eval_singletonP, @eval_consP).

Lemma eval_eq {p A B} : A ≡ B -> eval p A = eval p B.
Proof.
elim: A B; first by move=> B /eq_nilE ->.
move => a A IH B /copy [/eq_in_iff /(_ a) /iffLR].
apply: unnest; first by left.
move /(@in_split _ _) => [B1 [B2 ->]].
under (eq_lr eq_refl (B' := a :: (B1 ++ B2))).
{
by eq_trivial.
}
move /eq_cons_iff /IH.
rewrite ? eval_norm.
move=> ->.
by lia.
