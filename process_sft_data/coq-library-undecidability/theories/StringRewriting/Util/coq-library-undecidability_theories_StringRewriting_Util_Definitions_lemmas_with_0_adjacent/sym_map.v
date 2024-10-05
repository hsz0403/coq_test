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
eauto.
