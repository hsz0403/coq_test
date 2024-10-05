Set Implicit Arguments.
Require Import Lia List.
From Undecidability.HOU Require Import std.lists.basics std.misc std.enumerable std.decidable.
Import ListNotations.
Set Default Proof Using "Type".
Section Reductions.
Variable (X Y Z: Type).
Implicit Types (P: X -> Prop) (Q: Y -> Prop) (R: Z -> Prop).
Definition Neg {X} (P: X -> Prop) (x: X) := ~ P x.
Definition reduction {X Y: Type} (P: X -> Prop) (Q: Y -> Prop) := exists f, forall x, P x <-> Q (f x).
Notation "P ⪯ Q" := (reduction P Q) (at level 60).
End Reductions.
Hint Resolve reduction_reflexive reduction_transitive : core.
Notation "P ⪯ Q" := (reduction P Q) (at level 60).
Section enum_red.
Variables (X Y : Type) (p : X -> Prop) (q : Y -> Prop).
Variables (f : X -> Y) (Hf : forall x, p x <-> q (f x)).
Variables (Lq : _) (qe : enum q Lq).
Variables (x0 : X).
Variables (d : Dis Y).
Fixpoint L (LX : enumT X) n := match n with | 0 => [] | S n => L LX n ++ [ x | x ∈ L_T X n, (f x ∈ Lq n) ] end.
End enum_red.
Section enum_red2.
Variables (X Y Z : Type) (p : X -> Prop) (q : Y -> Prop).
Variables (f : X -> Y) (Hf : forall x, p x <-> q (f x)).
Variables (g: Y -> Z) (Hg: forall y1 y2, g y1 = g y2 -> q y1 <-> q y2).
Variables (Lq : _) (qe : enum q Lq).
Variables (d : Dis Z).
Variable (LX: enumT X).
Fixpoint Lalt n := match n with | 0 => [] | S n => Lalt n ++ [ x | x ∈ L_T X n, (g (f x) ∈ map g (Lq n)) ] end.
End enum_red2.

Lemma reduction_transitive P Q R: P ⪯ Q -> Q ⪯ R -> P ⪯ R.
Proof.
intros [f H1] [g H2]; exists (f >> g).
intros x; rewrite H1, H2.
reflexivity.
