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

Lemma hash_R_app x y : #_R (x ++ y) = #_R x ++ #_R y.
Proof.
induction x; cbn in *; now try rewrite IHx.
