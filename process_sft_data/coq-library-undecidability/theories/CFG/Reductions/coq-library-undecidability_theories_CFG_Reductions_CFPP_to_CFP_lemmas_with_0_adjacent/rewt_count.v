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

Lemma rewt_count x : rewt G [S] x -> count x S <= 1.
Proof.
induction 1.
-
cbn.
now rewrite Nat.eqb_refl.
-
inv H0.
destruct H1 as [ | [ [[] []] % in_map_iff | [[] []] % in_map_iff ] % in_app_iff]; inv H0.
+
eauto.
+
unfold Sigma.
simpl_list.
rewrite <- !countSplit in *.
cbn in *.
rewrite Nat.eqb_refl in *.
enough (count l S = 0) as ->.
enough (count l0 S = 0) as ->.
lia.
*
eapply notInZero.
intros D.
edestruct (fresh_spec) with (l := Sigma); try reflexivity.
eapply sym_word_R in H1.
unfold Sigma.
eauto.
*
eapply notInZero.
intros D.
edestruct (fresh_spec) with (l := Sigma); try reflexivity.
eapply sym_word_l in H1.
unfold Sigma.
eauto.
+
unfold Sigma.
simpl_list.
rewrite <- !countSplit in *.
cbn in *.
rewrite Nat.eqb_refl in *.
assert (S =? a = false) as ->.
eapply Nat.eqb_neq.
intros D.
edestruct fresh_spec with (l := Sigma); try reflexivity.
unfold S in *.
rewrite D.
unfold Sigma; eauto.
enough (count l S = 0) as ->.
enough (count l0 S = 0) as ->.
lia.
*
eapply notInZero.
intros D.
edestruct (fresh_spec) with (l := Sigma); try reflexivity.
eapply sym_word_R in H1.
unfold Sigma.
eauto.
*
eapply notInZero.
intros D.
edestruct (fresh_spec) with (l := Sigma); try reflexivity.
eapply sym_word_l in H1.
unfold Sigma.
eauto.
