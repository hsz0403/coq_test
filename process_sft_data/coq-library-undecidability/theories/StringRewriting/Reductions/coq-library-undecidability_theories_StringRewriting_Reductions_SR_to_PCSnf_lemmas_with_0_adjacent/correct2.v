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

Lemma correct2 x1 x2 y1 y2 : incl x1 Σ -> incl x2 Σ -> incl y1 Σ -> incl y2 Σ -> PCSnf (R', x2 ++ [#] ++ x1, y2 ++ [#] ++ y1) -> SR (R, x1 ++ x2, y1 ++ y2).
Proof.
intros Hx1 Hx2 Hy1 Hy2.
remember (x2 ++ [#] ++ x1) as x.
remember (y2 ++ [#] ++ y1) as y.
induction 1 in x1, x2, y1, y2, Heqx, Heqy, Hx1, Hx2, Hy1, Hy2; subst.
-
eapply list_prefix_inv in Heqy as [-> -> ].
econstructor.
unfold Σ in *.
+
now intros ? % Hx2 % fresh_spec.
+
now intros ? % Hy2 % fresh_spec.
-
inversion H as [x u v [H2 | (a & Ha & H2) % in_map_iff] % in_app_iff H1 H3]; subst y.
+
assert (In # x) as Hx.
{
assert (In # (x2 ++ # :: x1)) as Hf by eauto.
rewrite <- H1 in Hf.
eapply in_app_iff in Hf as [ | ]; [ | now eauto].
eapply sym_word_l in H3; eauto.
exfalso.
eapply fresh_spec with (l := Σ).
2:reflexivity.
unfold Σ at 2.
eauto.
}
eapply in_split in Hx as (x1_ & x2_ & ->).
replace (u ++ x1_ ++ [#] ++ x2_) with ((u ++ x1_) ++ [#] ++ x2_) in H1 by now simpl_list.
eapply list_prefix_inv in H1 as (<- & ->).
*
econstructor.
econstructor.
eauto.
replace (x1 ++ v ++ x1_) with ((x1 ++ v) ++ x1_) by now simpl_list.
eapply IHderv.
--
eapply incl_app.
eauto.
unfold Σ.
eauto.
--
etransitivity; eauto.
--
eauto.
--
eauto.
--
now simpl_list.
--
now simpl_list.
*
eapply use_fresh.
eapply incl_app.
unfold Σ.
eauto.
eapply list_prefix_inv'' in H1 as [<- <-].
2: eapply use_fresh; eauto.
2: eapply use_fresh; eauto.
etransitivity; eauto.
*
eapply use_fresh.
eauto.
+
inversion Ha; subst; clear Ha.
destruct H2 as [<- | H2].
*
eapply list_prefix_inv with (x := []) in H1 as [<- <-]; [ | firstorder | now eapply use_fresh].
simpl_list.
cbn in H.
eapply (IHderv []); [ eauto .. | now simpl_list ].
*
assert (In # x) as Hx.
{
assert (In # (x2 ++ # :: x1)) as Hf by eauto.
rewrite <- H1 in Hf.
eapply in_app_iff in Hf as [ | ]; [ | now eauto].
exfalso.
destruct H3 as [-> | []].
eapply fresh_spec with (l := Σ); eauto.
}
eapply in_split in Hx as (x1_ & x2_ & ->).
replace ([a] ++ x1_ ++ [#] ++ x2_) with (([a] ++ x1_) ++ [#] ++ x2_) in H1 by now simpl_list.
eapply list_prefix_inv in H1 as (<- & ->).
--
replace (x1 ++ [a] ++ x1_) with ((x1 ++ [a]) ++ x1_) by now simpl_list.
eapply IHderv.
++
eapply incl_app.
eauto.
eauto.
++
etransitivity; eauto.
++
eauto.
++
eauto.
++
now simpl_list.
++
now simpl_list.
--
eapply use_fresh.
eapply incl_app.
eauto.
eapply list_prefix_inv'' in H1 as [<- <-].
2: eapply use_fresh; eauto.
2: eapply use_fresh; eauto.
etransitivity; eauto.
--
eapply use_fresh.
eauto.
