Require Import List Lia.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts typing_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Arguments nth_error_In {A l n x}.
Local Arguments In_nth_error {A l x}.
Definition iipc2 (Gamma: environment) (t: poly_type) := exists P, typing Gamma P t.
Arguments iipc2 : simpl never.

Lemma iipc2_poly_absI (x: nat) {Gamma t} : Forall (fresh_in x) Gamma -> fresh_in (S x) t -> iipc2 Gamma (ren_poly_type (scons x id) t) -> iipc2 Gamma (poly_abs t).
Proof.
pose ξ := fun y => if PeanoNat.Nat.eq_dec x y then 0 else S y.
move=> HG Ht /(iipc2_ren_poly_type ξ).
have -> : map (ren_poly_type ξ) Gamma = (map (ren_poly_type S) Gamma).
{
elim: Gamma HG; first done.
move=> s Gamma H /Forall_consP [Hx /H{H} /= ->].
congr cons.
apply: ext_ren_poly_type_allfv_poly_type.
apply: allfv_poly_type_impl Hx => ? ?.
rewrite /ξ.
by case: (PeanoNat.Nat.eq_dec _ _).
}
move=> [?] /typing_ty_abs /iipc2I.
congr iipc2.
congr poly_abs.
rewrite poly_type_norm /ξ /= ren_poly_type_allfv_id; last done.
apply: allfv_poly_type_impl Ht.
clear.
move=> [|y]; case: (PeanoNat.Nat.eq_dec _ _); move=> /=; by lia.
