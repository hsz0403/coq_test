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

Lemma copy u v : incl u Σ -> derv R' (u ++ v) (v ++ u).
Proof.
intros Hu.
induction u in v, Hu |- *; cbn.
-
simpl_list.
constructor.
-
replace (a :: u ++ v) with ([a] ++ (u ++ v)) by reflexivity.
replace (v ++ rev u ++ [a]) with ((v ++ rev u) ++ [a]) by now simpl_list.
econstructor.
constructor.
eapply in_app_iff.
right.
eapply in_map_iff.
eauto.
simpl_list.
replace (v ++ a :: u) with ((v ++ [a]) ++ u) by now simpl_list.
eapply IHu.
eauto.
