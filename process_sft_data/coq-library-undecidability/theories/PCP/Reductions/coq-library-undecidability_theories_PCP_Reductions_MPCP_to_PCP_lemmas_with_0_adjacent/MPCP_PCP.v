Require Import Bool List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Shared.ListAutomation.
Set Default Proof Using "Type".
Section MPCP_PCP.
Local Definition card := card nat.
Local Definition string := string nat.
Local Notation "x / y" := (x, y).
Variable R : list (card).
Variable x0 y0 : string.
Definition Sigma := sym (x0/y0 :: R).
Definition R_Sigma : sym R <<= Sigma.
Proof.
unfold Sigma.
cbn.
eauto.
Definition dollar := fresh Sigma.
Notation "$" := dollar.
Definition hash := fresh (dollar :: Sigma).
Notation "#" := hash.
Fixpoint hash_l (x : string) := match x with | [] => [] | a :: x => # :: a :: hash_l x end.
Notation "#_L" := hash_l.
Fixpoint hash_r (x : string) := match x with | [] => [] | a :: x => a :: # :: hash_r x end.
Notation "#_R" := hash_r.
Definition d := ($ :: (#_L x0)) / ($ :: # :: (#_R y0)).
Definition e := [#;$] / [$].
Definition P := [d;e] ++ map (fun '(x,y) => (#_L x, #_R y)) (filter (fun '(x,y) => is_cons x || is_cons y) (x0/y0::R)).
End MPCP_PCP.

Lemma MPCP_PCP x y A : A <<= x0/y0 :: R -> x ++ tau1 A = y ++ tau2 A -> exists B, B <<= P /\ (#_L x) ++ tau1 B = # :: #_R y ++ tau2 B.
Proof.
revert x y; induction A; cbn -[fresh P] in *; intros.
-
rewrite !app_nil_r in H0.
subst.
exists [e].
firstorder.
cbn -[fresh].
enough ((#_L y ++ [#]) ++ [$] = # :: #_R y ++ [$]) by now autorewrite with list in *.
now rewrite hash_swap.
-
destruct a as (x', y').
assert ( (x ++ x') ++ tau1 A = (y ++ y') ++ tau2 A) by now simpl_list.
eapply IHA in H1 as (B & ? & ?) ; [ | firstorder].
rewrite hash_L_app, hash_R_app in H2.
autorewrite with list in H2.
destruct (is_cons x' || is_cons y') eqn:E.
+
exists ( (#_L x' / #_R y') :: B).
split.
*
intros ? [ <- | ]; [ | eauto].
unfold P.
rewrite in_app_iff, in_map_iff.
right.
exists (x', y').
eauto.
*
eassumption.
+
exists B.
rewrite orb_false_iff, <- !not_true_iff_false, !is_cons_true_iff in E.
destruct E.
destruct x', y'; firstorder congruence.
