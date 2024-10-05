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

Lemma compactness_value_1d : forall a b (delta : R -> posreal), { d : posreal | forall x, a <= x <= b -> ~~ exists t, a <= t <= b /\ Rabs (x - t) < delta t /\ d <= delta t }.
Proof.
intros a b delta.
destruct (compactness_value 1 (a,tt) (b,tt) (fun t => let '(t,_) := t in delta t)) as (d, Hd).
exists d.
intros x Hx.
specialize (Hd (x,tt) (conj Hx I)).
do 2 contradict Hd.
destruct Hd as ((t,t'),Ht).
exists t.
repeat split ; apply Ht.
