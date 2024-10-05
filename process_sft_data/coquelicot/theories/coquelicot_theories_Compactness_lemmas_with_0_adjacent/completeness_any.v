Require Import Reals.
Require Import mathcomp.ssreflect.ssreflect.
Require Import List.
Require Import Rcomplements.
Open Scope R_scope.
Section Compactness.
Fixpoint Tn n T : Type := match n with | O => unit | S n => (T * Tn n T)%type end.
Fixpoint bounded_n n : Tn n R -> Tn n R -> Tn n R -> Prop := match n return Tn n R -> Tn n R -> Tn n R -> Prop with | O => fun a b x : Tn O R => True | S n => fun a b x : Tn (S n) R => let '(a1,a2) := a in let '(b1,b2) := b in let '(x1,x2) := x in a1 <= x1 <= b1 /\ bounded_n n a2 b2 x2 end.
Fixpoint close_n n d : Tn n R -> Tn n R -> Prop := match n return Tn n R -> Tn n R -> Prop with | O => fun x t : Tn O R => True | S n => fun x t : Tn (S n) R => let '(x1,x2) := x in let '(t1,t2) := t in Rabs (x1 - t1) < d /\ close_n n d x2 t2 end.
End Compactness.

Lemma completeness_any : forall P : R -> Prop, ( forall x y, x <= y -> P y -> P x ) -> forall He : (exists x, P x), forall Hb : (bound P), forall x, x < proj1_sig (completeness _ Hb He) -> ~ ~ P x.
Proof.
intros P HP He Hb x.
case completeness => y [Hy1 Hy2] /= Hxy Px.
apply Rle_not_lt with (2 := Hxy).
apply Hy2 => t Pt.
apply Rnot_lt_le => Hxt.
apply Px.
apply: HP Pt.
now apply Rlt_le.
