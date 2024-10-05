Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC.
Require Import Undecidability.PolynomialConstraints.LPolyNC.
Require Import Undecidability.Synthetic.Definitions.
From Undecidability.PolynomialConstraints.Util Require Import Facts PolyFacts.
Require Undecidability.SetConstraints.Util.mset_eq_utils.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Module Argument.
Local Arguments poly_add !p !q.
Local Notation "p ≃ q" := (poly_eq p q) (at level 65).
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Definition encode_msetc (c : msetc) : polyc := match c with | msetc_zero x => polyc_one x | msetc_sum x y z => polyc_sum x y z | msetc_h x y => polyc_prod x y end.
Fixpoint mset_to_poly (A: list nat) := match A with | [] => [] | a :: A => poly_add (repeat 0 a ++ [1]) (mset_to_poly A) end.
Fixpoint poly_to_mset (p: list nat) := match p with | [] => [] | a :: p => (repeat 0 a) ++ map S (poly_to_mset p) end.
End Argument.

Lemma mset_to_poly_mapP {A} : mset_to_poly (map S A) ≃ 0 :: mset_to_poly A.
Proof.
elim: A; first by (case; [done | by case]).
move=> a A + i => /(_ i).
case: i.
-
by rewrite /map -/(map _ _) ?poly_add_nthP.
-
move=> i.
rewrite /map -/(map _ _) /mset_to_poly -/(mset_to_poly).
rewrite /= ?poly_add_nthP /=.
by lia.
