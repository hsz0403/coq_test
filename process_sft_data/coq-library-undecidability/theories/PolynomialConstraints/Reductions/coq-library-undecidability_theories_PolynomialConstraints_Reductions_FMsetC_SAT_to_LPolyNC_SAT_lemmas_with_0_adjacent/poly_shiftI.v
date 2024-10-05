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

Lemma poly_shiftI {p} : (0 :: p) ≃ poly_mult [0; 1] p.
Proof.
rewrite /poly_mult map_0P.
rewrite [poly_add (repeat _ _) _] poly_add_comm.
apply: poly_add_0I; first by apply: repeat_0P.
under map_ext => a do have -> : 1 * a = a by lia.
rewrite -/(poly_eq _ _) map_id.
apply: poly_eq_consI; first done.
apply: poly_add_0I; last done.
by apply: (repeat_0P (n := 1)).
