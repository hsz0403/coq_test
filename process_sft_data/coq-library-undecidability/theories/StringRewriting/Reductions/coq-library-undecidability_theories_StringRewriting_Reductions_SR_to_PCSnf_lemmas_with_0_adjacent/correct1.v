Require Import List.
Import ListNotations.
Require Import Undecidability.StringRewriting.PCSnf.
Require Import Undecidability.StringRewriting.SR.
Require Import Undecidability.StringRewriting.Util.Definitions.
Set Default Proof Using "Type".
Section fix_R.
Variable R : SRS nat.
Variables x0 y0 : list nat.
Definition Σ := x0 ++ y0 ++ sym R.
Notation "#" := (fresh Σ).
Definition R' := R ++ map (fun a => ([a], [a])) (# :: Σ).
Hint Unfold Σ : core.
End fix_R.
Require Import Undecidability.Synthetic.Definitions.

Lemma correct1 x y : incl x Σ -> incl y Σ -> SR (R, x, y) -> PCSnf (R', x ++ [#], y ++ [#]).
Proof.
intros Hx Hy.
cbn.
induction 1 as [ | x' y'].
-
constructor.
-
inversion H as [ x y u v H1 H2 H3 ]; subst x' y'.
simpl_list.
eapply derv_trans.
1: eapply copy; eauto.
simpl_list.
econstructor.
{
econstructor.
eapply in_app_iff.
eauto.
}
simpl_list.
eapply derv_trans.
1: eapply copy; eauto.
simpl_list.
econstructor.
{
econstructor.
eapply in_app_iff.
eauto.
}
eapply IHrewt; [ | eauto].
eapply incl_app; [ eauto | ].
eapply incl_app; [ | eauto ].
unfold Σ.
eauto.
