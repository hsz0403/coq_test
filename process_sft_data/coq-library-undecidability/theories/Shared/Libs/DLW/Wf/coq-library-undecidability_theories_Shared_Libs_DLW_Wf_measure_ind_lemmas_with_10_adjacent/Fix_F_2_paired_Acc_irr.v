Require Import Arith Lia Wellfounded List Extraction.
From Undecidability.Shared.Libs.DLW.Wf Require Import acc_irr.
Set Implicit Arguments.
Section measure_rect.
Variable (X : Type) (m : X -> nat) (P : X -> Type).
Hypothesis F : forall x, (forall x', m x' < m x -> P x') -> P x.
Arguments F : clear implicits.
Let R x y := m x < m y.
Let Rwf : forall x : X, Acc R x.
Proof.
apply wf_inverse_image with (f := m), lt_wf.
Let Fix_F : forall x : X, Acc R x -> P x.
Proof.
refine( fix Fix_F x (H : Acc R x) { struct H } := F x (fun x' (H' : R x' x) => Fix_F x' _) ).
destruct H as [ G ].
apply G.
trivial.
Defined.
Let Fix_F_fix x A : @Fix_F x A = F x (fun y H => Fix_F (Acc_inv A H)).
Proof.
destruct A; reflexivity.
Definition measure_rect x : P x := Fix_F (Rwf x).
Hypothesis F_ext : forall x f g, (forall y H, f y H = g y H) -> F x f = F x g.
Let Fix_F_Acc_irr : forall x f g, @Fix_F x f = Fix_F g.
Proof.
apply Acc_irrelevance.
intros; apply F_ext; auto.
End measure_rect.
Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) := pattern x; revert x; apply measure_rect with (m := fun x => f); intros x IH.
Extraction Inline measure_rect.
Section measure_double_rect.
Variable (X Y : Type) (m : X -> Y -> nat) (P : X -> Y -> Type).
Hypothesis F : (forall x y, (forall x' y', m x' y' < m x y -> P x' y') -> P x y).
Let m' (c : X * Y) := match c with (x,y) => m x y end.
Let R c d := m' c < m' d.
Let Rwf : well_founded R.
Proof.
apply wf_inverse_image with (f := m'), lt_wf.
Section measure_double_rect_paired.
Let Q c := match c with (x,y) => P x y end.
Definition measure_double_rect x y : P x y := Fix_F_2 (Rwf (_,_)).
Hypothesis F_ext : forall x y f g, (forall x' y' H, f x' y' H = g x' y' H) -> @F x y f = F g.
Let Fix_F_2_paired c (A : Acc R c) : P (fst c) (snd c).
Proof.
destruct c; simpl; apply Fix_F_2; trivial.
Defined.
Let Fix_F_2_paired_Acc_irr : forall c f g, @Fix_F_2_paired c f = Fix_F_2_paired g.
Proof.
apply Acc_irrelevance.
intros (x,y) f g IH; apply F_ext.
intros x' y' ?; apply (@IH (x',y')).
Let Fix_F_2_Acc_irr x y f g : @Fix_F_2 x y f = Fix_F_2 g.
Proof.
intros; apply (@Fix_F_2_paired_Acc_irr (x,y)); trivial.
End measure_double_rect.
End measure_double_rect.
Tactic Notation "paired" "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) := pattern x, y; revert x y; apply measure_double_rect_paired with (m := fun x y => f); intros x y IH.
Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) := pattern x, y; revert x y; apply measure_double_rect with (m := fun x y => f); intros x y IH.
Extraction Inline measure_double_rect measure_double_rect_paired.

Let Rwf : forall x : X, Acc R x.
Proof.
Admitted.

Let Fix_F : forall x : X, Acc R x -> P x.
Proof.
refine( fix Fix_F x (H : Acc R x) { struct H } := F x (fun x' (H' : R x' x) => Fix_F x' _) ).
destruct H as [ G ].
apply G.
Admitted.

Let Fix_F_fix x A : @Fix_F x A = F x (fun y H => Fix_F (Acc_inv A H)).
Proof.
Admitted.

Let Fix_F_Acc_irr : forall x f g, @Fix_F x f = Fix_F g.
Proof.
apply Acc_irrelevance.
Admitted.

Theorem measure_rect_fix x : measure_rect x = @F x (fun y _ => measure_rect y).
Proof.
unfold measure_rect; rewrite Fix_F_fix.
apply F_ext.
Admitted.

Let Rwf : well_founded R.
Proof.
Admitted.

Theorem measure_double_rect_paired x y : P x y.
Proof.
change (Q (x,y)).
generalize (x,y); clear x y; intros c.
induction on c as IH with measure (m' c).
destruct c as (x,y); apply F.
Admitted.

Let Fix_F_2 : forall x y, Acc R (x,y) -> P x y.
Proof.
refine (fix Fix_F_2 x y H { struct H } := @F x y (fun x' y' H' => Fix_F_2 x' y' _) ).
destruct H as [ H ]; unfold R in H at 1.
apply H.
Admitted.

Let Fix_F_2_fix x y H : @Fix_F_2 x y H = F (fun x' y' H' => Fix_F_2 (@Acc_inv _ _ _ H (x',y') H')).
Proof.
Admitted.

Let Fix_F_2_paired c (A : Acc R c) : P (fst c) (snd c).
Proof.
Admitted.

Let Fix_F_2_Acc_irr x y f g : @Fix_F_2 x y f = Fix_F_2 g.
Proof.
Admitted.

Theorem measure_double_rect_fix x y : measure_double_rect x y = @F x y (fun x' y' _ => measure_double_rect x' y').
Proof.
unfold measure_double_rect; rewrite Fix_F_2_fix.
apply F_ext.
Admitted.

Let Fix_F_2_paired_Acc_irr : forall c f g, @Fix_F_2_paired c f = Fix_F_2_paired g.
Proof.
apply Acc_irrelevance.
intros (x,y) f g IH; apply F_ext.
intros x' y' ?; apply (@IH (x',y')).
