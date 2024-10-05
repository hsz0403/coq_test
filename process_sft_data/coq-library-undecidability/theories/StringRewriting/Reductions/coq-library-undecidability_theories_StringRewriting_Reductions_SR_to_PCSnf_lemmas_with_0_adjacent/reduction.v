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

Lemma reduction : SR ⪯ PCSnf.
Proof.
exists (fun '(R,x,y) => (R' R x y, x ++ fresh (Σ R x y), y ++ fresh (Σ R x y))).
intros [[R x] y].
split.
-
eapply correct1; unfold Σ; eauto.
-
intros.
eapply correct2 with (x0 := x) (y0 := y) (x1 := []) (y1 := []).
1-4: unfold Σ; eauto.
now simpl_list.
