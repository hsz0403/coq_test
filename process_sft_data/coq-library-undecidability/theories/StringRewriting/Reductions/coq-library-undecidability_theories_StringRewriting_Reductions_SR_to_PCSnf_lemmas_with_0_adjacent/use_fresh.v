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

Lemma use_fresh {Σ} x : incl x Σ -> ~ In (fresh Σ) x.
Proof.
now intros H ? % H % fresh_spec.
