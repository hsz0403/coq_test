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

Lemma completeness {l} : FMsetC_SAT l -> LPolyNC_SAT (map encode_msetc l).
Proof.
move=> [φ].
rewrite -Forall_forall => Hφ.
exists (fun x => mset_to_poly (φ x)).
rewrite -Forall_forall Forall_mapP.
apply: Forall_impl; last by eassumption.
case.
-
by move=> x /= /mset_eq_utils.eq_symm /mset_eq_utils.eq_singletonE ->.
-
move=> x y z /= /mset_to_poly_eqI.
move /poly_eq_trans.
apply.
by apply mset_to_poly_appP.
-
move=> x y /= /mset_to_poly_eqI.
move /poly_eq_trans.
apply.
apply: (poly_eq_trans _ poly_shiftI).
by apply: mset_to_poly_mapP.
