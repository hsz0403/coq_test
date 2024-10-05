Set Implicit Arguments.
From Undecidability.HOU Require Import std.misc std.decidable.
Set Default Proof Using "Type".
Class retract (X Y: Type) := { I: X -> Y; R: Y -> option X; retr: forall x, R (I x) = Some x }.
Instance retract_refl X: retract X X.
Proof.
exists (@id X) Some.
reflexivity.
Instance retract_trans X Y Z: retract X Y -> retract Y Z -> retract X Z.
Proof.
intros H1 H2.
exists (I >> I) (fun z => match R z with Some y => R y | None => None end).
intros x; unfold funcomp; now rewrite !retr.
Instance retract_False X: retract False X.
Proof.
exists (fun f: False => match f with end) (fun _ => None).
intros [].
Require Import FinFun.
Section Properties.
Variable (X Y: Type).
Variable (r: retract X Y).
Context {D: Dis Y}.
Global Instance dis_retract: Dis X.
Proof using r Y D.
intros x y.
destruct (I x == I y) as [H|H].
-
left; eapply (f_equal R) in H; rewrite !retr in H.
now injection H as ->.
-
right; intros ->; now eapply H.
Definition tight (y: Y) := match R y with | Some x => if I x == y then Some x else None | None => None end.
End Properties.

Instance retract_refl X: retract X X.
Proof.
exists (@id X) Some.
Admitted.

Instance retract_trans X Y Z: retract X Y -> retract Y Z -> retract X Z.
Proof.
intros H1 H2.
exists (I >> I) (fun z => match R z with Some y => R y | None => None end).
Admitted.

Instance retract_False X: retract False X.
Proof.
exists (fun f: False => match f with end) (fun _ => None).
Admitted.

Lemma tight_is_tight x y: tight y = Some x -> I x = y.
Proof.
unfold tight.
destruct R.
destruct (I x0 == y).
all: try discriminate.
Admitted.

Lemma tight_retr x: tight (I x) = Some x.
Proof.
Admitted.

Lemma retract_injective: Injective I.
Proof.
intros x y H % (f_equal R).
rewrite !retr in H.
now injection H as ->.
