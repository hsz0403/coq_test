Require Import List.
Import ListNotations.
Require Import Undecidability.CFG.CFP.
Require Import Undecidability.CFG.CFG.
Require Import Undecidability.CFG.Util.Facts.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Shared.ListAutomation.
Require Import Undecidability.Synthetic.Definitions.
Require Import Setoid Morphisms Arith Lia.
Set Default Proof Using "Type".
Hint Rewrite concat_app map_app map_map : list.
Hint Rewrite <- map_rev : list.
Definition gamma (A : stack nat) := map (fun '(x,y) => (x, rev y)) A.
Section CFGs.
Global Instance rewtTrans R : PreOrder (rewt R).
Proof.
split.
-
hnf.
econstructor.
-
induction 2; eauto.
Global Instance rewrite_proper R : Proper (rewt R ==> rewt R ==> rewt R) (@app sig).
Proof.
intros x1 y1 H1 x2 y2 H2.
induction H1.
-
induction H2.
+
reflexivity.
+
rewrite IHrewt.
inv H.
eapply rewtRule.
replace (x1 ++ x ++ [a] ++ y0) with ( (x1 ++ x) ++ [a] ++ y0) by now autorewrite with list.
eauto.
replace (x1 ++ x ++ v ++ y0) with ( (x1 ++ x) ++ v ++ y0) by now autorewrite with list.
eauto.
-
rewrite IHrewt.
inv H.
autorewrite with list.
eauto.
Global Instance subrel R : subrelation (rew_cfg R) (rewt R).
Proof.
intros x y H.
econstructor.
reflexivity.
eassumption.
Definition sym_G (G : cfg) := startsym G :: flat_map (fun '(a, x) => a :: x) (rules G).
End CFGs.
Section Post_CFG.
Variable R : stack nat.
Variable a : nat.
Definition Sigma := sym R ++ [a].
Definition S : nat := fresh Sigma.
Definition G := (S, (S,[S]) :: map (fun '(u, v) => (S, u ++ [S] ++ v)) R ++ map (fun '(u, v) => (S, u ++ [a] ++ v)) R).
End Post_CFG.

Lemma Post_CFG_2 x : rewt G [S] x -> exists A m, A <<= R /\ sigma m A = x /\ (m = S \/ m = a /\ A <> []).
Proof.
intros.
induction H.
-
cbn.
exists [], S.
eauto.
-
inv H0.
destruct H1 as [ | [(? & ? & ?) % in_map_iff | (? & ? & ?) % in_map_iff] % in_app_iff]; inv H0.
+
eassumption.
+
destruct x0 as [u' v'].
inv H3.
destruct IHrewt as (A & m & HA & IHA & Hm).
exists (A ++ [(u', v')]), S.
repeat split.
*
eauto.
*
simpl_list.
cbn.
enough (~ S el x).
enough (~ S el y0).
eapply sigma_snoc with (s := S); eauto.
--
assert (IH2 := IHA).
eapply sigma_inv in IHA; eauto.
subst.
eauto.
intros D.
edestruct fresh_spec with (l := sym R ++ [a]); try reflexivity.
eapply in_app_iff.
left.
eapply sym_mono.
eauto.
eauto.
--
eapply rewt_count in H.
rewrite <- !countSplit in H.
cbn in H.
rewrite Nat.eqb_refl in H.
eapply notInZero.
lia.
--
eapply rewt_count in H.
rewrite <- !countSplit in H.
cbn in H.
rewrite Nat.eqb_refl in H.
eapply notInZero.
lia.
*
eauto.
+
destruct x0 as [u' v'].
inv H3.
destruct IHrewt as (A & m & HA & IHA & Hm).
exists (A ++ [(u', v')]), a.
repeat split.
*
eauto.
*
simpl_list.
cbn.
enough (~ S el x).
enough (~ S el y0).
eapply sigma_snoc with (s := S); eauto.
--
assert (IH2 := IHA).
eapply sigma_inv in IHA; eauto.
subst.
eauto.
intros D.
edestruct fresh_spec with (l := sym R ++ [a]); try reflexivity.
eapply in_app_iff.
left.
eapply sym_mono.
eauto.
eauto.
--
eapply rewt_count in H.
rewrite <- !countSplit in H.
cbn in H.
rewrite Nat.eqb_refl in H.
eapply notInZero.
lia.
--
eapply rewt_count in H.
rewrite <- !countSplit in H.
cbn in H.
rewrite Nat.eqb_refl in H.
eapply notInZero.
lia.
*
destruct A; cbn; firstorder congruence.
