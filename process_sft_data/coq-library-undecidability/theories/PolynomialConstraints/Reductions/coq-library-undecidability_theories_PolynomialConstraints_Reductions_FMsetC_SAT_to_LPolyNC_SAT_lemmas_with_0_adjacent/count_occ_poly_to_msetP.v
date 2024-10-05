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

Lemma count_occ_poly_to_msetP {a p}: count_occ Nat.eq_dec (poly_to_mset p) a = nth a p 0.
Proof.
elim: a p.
-
case; first done.
move=> + p /=.
elim; first by elim: (poly_to_mset p).
by move=> ? /= ->.
-
move=> i IH.
case; first done.
move=> a p /=.
rewrite count_occ_app.
rewrite -(count_occ_map S Nat.eq_dec) ?IH; first by lia.
by elim a.
