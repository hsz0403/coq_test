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

Lemma mset_to_poly_shift {a A B} : mset_to_poly (A ++ a :: B) ≃ mset_to_poly (a :: A ++ B).
Proof.
elim: A; first done.
move=> c A + i => /(_ i) /=.
rewrite ?poly_add_nthP.
Admitted.

Lemma mset_to_poly_appP {A B} : mset_to_poly (A ++ B) ≃ poly_add (mset_to_poly A) (mset_to_poly B).
Proof.
elim: A; first done.
move=> a A + i => /(_ i) /=.
rewrite ?poly_add_nthP.
Admitted.

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
Admitted.

Lemma poly_add_0I {p q r} : r ≃ [] -> p ≃ q -> p ≃ poly_add q r.
Proof.
move=> + + i => /(_ i) + /(_ i).
rewrite poly_add_nthP.
Admitted.

Lemma poly_shiftI {p} : (0 :: p) ≃ poly_mult [0; 1] p.
Proof.
rewrite /poly_mult map_0P.
rewrite [poly_add (repeat _ _) _] poly_add_comm.
apply: poly_add_0I; first by apply: repeat_0P.
under map_ext => a do have -> : 1 * a = a by lia.
rewrite -/(poly_eq _ _) map_id.
apply: poly_eq_consI; first done.
apply: poly_add_0I; last done.
Admitted.

Lemma mset_to_poly_eqI {A B} : A ≡ B -> mset_to_poly A ≃ mset_to_poly B.
Proof.
elim: A B.
-
by move=> B /mset_eq_utils.eq_nilE ->.
-
move=> a A IH B /mset_eq_utils.eq_consE [B1 [B2 [-> /IH {}IH]]].
apply: poly_eq_sym.
apply: (poly_eq_trans mset_to_poly_shift) => /=.
move=> i.
move: (IH i).
rewrite ?poly_add_nthP.
Admitted.

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
Admitted.

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
Admitted.

Lemma poly_to_mset_addP {p q} : poly_to_mset (poly_add p q) ≡ poly_to_mset p ++ poly_to_mset q.
Proof.
move=> a.
Admitted.

Lemma poly_to_mset_consP {p} : poly_to_mset (0 :: p) = map S (poly_to_mset p).
Proof.
Admitted.

Lemma soundness {l} : LPolyNC_SAT (map encode_msetc l) -> FMsetC_SAT l.
Proof.
move=> [ψ].
rewrite -Forall_forall Forall_mapP => Hψ.
exists (fun x => poly_to_mset (ψ x)).
rewrite -Forall_forall.
apply: Forall_impl; last by eassumption.
case.
-
by move=> x /= /poly_to_mset_eqI.
-
move=> x y z /= /poly_to_mset_eqI.
move /mset_eq_utils.eq_trans.
apply.
by apply: poly_to_mset_addP.
-
move=> x y /= /poly_to_mset_eqI.
move /mset_eq_utils.eq_trans.
apply.
move: (ψ y) => p.
rewrite -poly_to_mset_consP.
apply: poly_to_mset_eqI.
apply: poly_eq_sym.
Admitted.

Theorem reduction : FMsetC_SAT ⪯ LPolyNC_SAT.
Proof.
exists (map Argument.encode_msetc) => l.
constructor.
-
exact Argument.completeness.
-
Admitted.

Lemma poly_to_mset_eqI {p q} : p ≃ q -> poly_to_mset p ≡ poly_to_mset q.
Proof.
move=> + a.
by rewrite ?count_occ_poly_to_msetP.
