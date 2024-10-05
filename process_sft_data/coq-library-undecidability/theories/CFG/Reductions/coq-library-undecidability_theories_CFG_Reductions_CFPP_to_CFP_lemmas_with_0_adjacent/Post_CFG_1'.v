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

Lemma Post_CFG_1' A : A <<= R -> A = [] \/ rewt G [S] (sigma a A).
Proof.
induction A.
-
cbn.
eauto.
-
intros.
assert (A <<= R) by eauto.
eapply IHA in H0.
destruct a0 as [u v].
destruct H0.
+
subst.
right.
erewrite rewrite_sing with (x := u ++ [a] ++ v).
reflexivity.
right.
eapply in_app_iff.
right.
eapply in_map_iff.
exists (u,v); eauto.
+
right.
erewrite rewrite_sing with (x := u ++ [S] ++ v).
now rewrite H0.
right.
eapply in_app_iff.
left.
eapply in_map_iff.
exists (u,v); eauto.
