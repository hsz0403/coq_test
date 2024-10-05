Require Import Undecidability.StringRewriting.SR.
Require Import Undecidability.Shared.ListAutomation.
Require Import Setoid Morphisms Lia.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Import RuleNotation.
Local Definition symbol := nat.
Local Definition string := (string nat).
Local Definition card : Type := (string * string).
Local Definition stack := list card.
Local Definition SRS := SRS nat.
Implicit Types a b : symbol.
Implicit Types x y z : string.
Implicit Types d e : card.
Implicit Types A R P : stack.
Coercion sing (n : nat) := [n].
Scheme rewt_ind' := Induction for rewt Sort Prop.
Instance PreOrder_rewt R : PreOrder (rewt R).
Proof.
split.
-
econstructor.
-
hnf.
intros.
induction H; eauto using rewR, rewS.
Instance Proper_rewt R : Proper (rewt R ==> rewt R ==> rewt R) (@app symbol).
Proof.
hnf.
intros.
hnf.
intros.
induction H.
-
now eapply rewt_app_L.
-
inv H.
transitivity (x1 ++ u ++ (y1 ++ x0)).
now simpl_list.
econstructor.
econstructor.
eassumption.
rewrite <- IHrewt.
now simpl_list.
Fixpoint sigma (a : symbol) A := match A with nil => [a] | x/y :: A => x ++ (sigma a A) ++ y end.
Fixpoint sym (R : list card) := match R with [] => [] | x / y :: R => x ++ y ++ sym R end.
Hint Resolve sym_word_l sym_word_R : core.
Fixpoint fresh (l : list nat) := match l with | [] => 0 | x :: l => S x + fresh l end.

Instance PreOrder_rewt R : PreOrder (rewt R).
Proof.
split.
-
econstructor.
-
hnf.
intros.
Admitted.

Lemma rewt_app_L R x x' y : rewt R x x' -> rewt R (y ++ x) (y ++ x').
Proof.
induction 1.
reflexivity.
inv H.
replace (y ++ x0 ++ u ++ y1) with ((y ++ x0) ++ u ++ y1).
econstructor.
econstructor.
eassumption.
simpl_list.
eassumption.
Admitted.

Instance Proper_rewt R : Proper (rewt R ==> rewt R ==> rewt R) (@app symbol).
Proof.
hnf.
intros.
hnf.
intros.
induction H.
-
now eapply rewt_app_L.
-
inv H.
transitivity (x1 ++ u ++ (y1 ++ x0)).
now simpl_list.
econstructor.
econstructor.
eassumption.
rewrite <- IHrewt.
Admitted.

Lemma rewt_subset R P x y : rewt R x y -> R <<= P -> rewt P x y.
Proof.
induction 1; intros.
-
reflexivity.
-
inv H.
eapply rewS; eauto.
eapply rewB.
Admitted.

Lemma rewt_left R x y z : rewt R x y -> rew R y z -> rewt R x z.
Proof.
induction 1; eauto.
+
intros.
eapply rewS; eauto.
eapply rewR.
+
intros.
Admitted.

Lemma rew_subset (R P : SRS) x y : rew R x y -> incl R P -> SR.rew P x y.
Proof.
intros H1 H2.
inversion H1; subst.
econstructor.
Admitted.

Lemma rew_app_inv (R1 R2 : SR.SRS nat) x y : SR.rew (R1 ++ R2) x y <-> SR.rew R1 x y \/ SR.rew R2 x y.
Proof.
split.
-
inversion 1 as [x0 y0 u v H0]; subst; eapply in_app_iff in H0 as [H0 | H0].
+
left.
econstructor.
eauto.
+
right.
econstructor.
eauto.
-
Admitted.

Lemma do_rew (R : SRS) x1 x2 x y u v : In (u, v) R -> x1 = x ++ u ++ y -> x2 = x ++ v ++ y -> rew R x1 x2.
Proof.
Admitted.

Lemma sym_app P R : sym (P ++ R) = sym P ++ sym R.
Proof.
induction P as [ | [] ]; eauto; cbn; rewrite IHP.
Admitted.

Lemma sym_map X (f : X -> card) l Sigma : (forall x : X, x el l -> sym [f x] <<= Sigma) -> sym (map f l) <<= Sigma.
Proof.
intros.
induction l as [ | ]; cbn in *.
-
firstorder.
-
pose proof (H a).
destruct f.
repeat eapply incl_app.
+
eapply app_incl_l, H0.
eauto.
+
eapply app_incl_l, app_incl_R; eauto.
+
Admitted.

Lemma sym_word_R R u v : u / v el R -> v <<= sym R.
Proof.
induction R; cbn; intros.
-
eauto.
-
destruct a as (u', v').
Admitted.

Lemma sym_mono A P : A <<= P -> sym A <<= sym P.
Proof.
induction A as [ | (x,y) ]; cbn; intros.
-
firstorder.
-
Admitted.

Lemma rewt_sym R x y Sigma: sym R <<= Sigma -> x <<= Sigma -> rewt R x y -> y <<= Sigma.
Proof.
intros.
induction H1.
-
eauto.
-
inv H1.
eapply IHrewt.
repeat eapply incl_app.
+
eapply app_incl_l.
eauto.
+
rewrite <- H.
eapply sym_word_R.
eauto.
+
eapply app_incl_R, app_incl_R.
Admitted.

Lemma fresh_spec' l a : a el l -> a < fresh l.
Proof.
induction l.
-
firstorder.
-
Admitted.

Lemma fresh_spec (a : symbol) (l : string) : a el l -> fresh l <> a.
Proof.
intros H % fresh_spec'.
intros <-.
Admitted.

Lemma sym_word_l R u v : u / v el R -> u <<= sym R.
Proof.
induction R; cbn; intros.
-
eauto.
-
destruct a as (u', v').
destruct H; try inv H; eauto.
