Require Import PeanoNat Lia List.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC.
From Undecidability.SetConstraints.Util Require Import Facts mset_eq_utils.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Definition eval p A := fold_right plus 0 (map (fun n => Nat.pow p n) A).
Definition eval_norm := (@eval_appP, @eval_singletonP, @eval_consP).

Lemma evalP {p A}: eval p A = fold_right plus 0 (map (fun n => Nat.pow p n) A).
Proof.
Admitted.

Lemma eval_consP {p a A} : eval p (a :: A) = p^a + eval p A.
Proof.
Admitted.

Lemma eval_singletonP {p a} : eval p [a] = p^a.
Proof.
cbn.
Admitted.

Lemma eval_appP {p A B} : eval p (A ++ B) = eval p A + eval p B.
Proof.
elim: A; first done.
move=> a A IH /=.
rewrite ? eval_consP.
Admitted.

Lemma eval_nat {p A} : Forall (fun a => 0 = a) A -> eval p A = length A.
Proof.
elim: A; first done.
move=> a A IH.
rewrite ? Forall_norm ? eval_consP /length - /(length _).
Admitted.

Lemma eval_monotone {p q A} : p < q -> eval p A < eval q A \/ Forall (fun a => 0 = a) A.
Proof.
move=> ?.
elim: A; first by right.
case.
{
move=> A IH.
rewrite ? eval_consP ? Forall_norm => /=.
case: IH=> IH; first by lia.
by right.
}
move=> a A IH.
left.
rewrite ? eval_consP.
have ? := Nat.pow_lt_mono_l p q (S a) ltac:(done) ltac:(done).
case: IH; first by lia.
move /eval_nat => H.
rewrite ? H.
Admitted.

Lemma eval_nat_spec {p q A} : p < q -> eval p A = eval q A -> Forall (fun a => 0 = a) A.
Proof.
move /eval_monotone => /(_ A).
Admitted.

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
Admitted.

Lemma eval_map {p A} : eval p (map S A) = p * eval p A.
Proof.
elim: A; first done.
move=> a A IH.
rewrite /map -/(map _ _) ? eval_consP IH.
rewrite /Nat.pow -/Nat.pow.
by nia.
