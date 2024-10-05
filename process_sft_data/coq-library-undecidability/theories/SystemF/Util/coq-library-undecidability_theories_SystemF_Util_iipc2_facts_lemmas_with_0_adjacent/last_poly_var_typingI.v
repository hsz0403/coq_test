Require Import List Lia.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts typing_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Arguments nth_error_In {A l n x}.
Local Arguments In_nth_error {A l x}.
Definition iipc2 (Gamma: environment) (t: poly_type) := exists P, typing Gamma P t.
Arguments iipc2 : simpl never.

Corollary last_poly_var_typingI {t Gamma}: (if last_poly_var t is Some x then In (poly_var x) Gamma else False) -> iipc2 Gamma t.
Proof.
move Hox: (last_poly_var t) => ox Hx.
case: ox Hox Hx; last done.
move=> x.
elim: t x Gamma.
-
move=> /= > [->] /In_nth_error [? ?].
eexists.
apply: typing_var.
by eassumption.
-
move=> ? _ ? IH > /= /IH H /H [P].
move=> /(@typing_ren_term' S) HP.
eexists.
apply: typing_abs.
by apply: HP.
-
move=> s + x Gamma /= => /(_ (S x) (map (ren_poly_type S) Gamma)).
case: (last_poly_var s); last done.
move=> [|y]; first done.
move=> + [?] ?.
subst y.
rewrite in_map_iff.
apply: unnest; first done.
apply: unnest.
{
eexists.
constructor; last by eassumption.
done.
}
move=> [?] /typing_ty_abs ?.
eexists.
by eassumption.
