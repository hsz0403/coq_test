Require Import List Arith Lia Bool.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat finite.
From Undecidability.PCP Require Import PCP.
Set Implicit Arguments.
Section dec.
Variable (X : Type) (eqX_dec : forall x y : X, { x = y } + { x <> y }).
Fact is_a_head_dec (l t : list X) : { x | l = t++x } + { ~ exists x, l = t++x }.
Proof.
revert t.
induction l as [ | a l IHl ].
+
intros [ | t ].
*
left; exists nil; auto.
*
right; intros ([ | ] & ?); discriminate.
+
intros [ | b t ].
*
left; exists (a::l); auto.
*
destruct (eqX_dec a b) as [ -> | C ].
-
destruct (IHl t) as [ H | C ].
++
left; destruct H as (x & ->).
exists x; auto.
++
right; contradict C; destruct C as (x & E).
exists x; inversion E; subst; auto.
-
right; contradict C; destruct C as (? & E); inversion E; auto.
Fact is_a_tail_dec (l t : list X) : { exists x, x++t = l } + { ~ exists x, x++t = l }.
Proof.
destruct (is_a_head_dec (rev l) (rev t)) as [ H | H ].
+
left; destruct H as (x & Hx).
exists (rev x).
apply f_equal with (f := @rev _) in Hx.
rewrite rev_app_distr in Hx.
do 2 rewrite rev_involutive in Hx; auto.
+
right; contradict H.
destruct H as (x & Hx); exists (rev x); subst.
apply rev_app_distr.
End dec.
Notation "R ⊳ s ∕ t" := (derivable R s t) (at level 70, format "R ⊳ s ∕ t").
Section pcp_hand_dec.
Variable (X : Type) (lc : list (list X * list X)).
Notation pcp_hand := (fun s t => lc ⊳ s∕t).
Section pcp_induction.
Implicit Type (l m : list X).
Definition strict_suffix x y l m := { a : _ & { b | (a <> nil \/ b <> nil) /\ l = a++x /\ m = b++y } }.
Variable (P : list X -> list X -> Type) (IHP : forall l m, (forall l' m', strict_suffix l' m' l m -> P l' m') -> P l m).
End pcp_induction.
Section bounded_dec.
Variable eqX_dec : forall x y : X, { x = y } + { x <> y }.
Let eqlX_dec : forall l m : list X, { l = m } + { l <> m }.
Proof.
apply list_eq_dec; auto.
Let eqXX_dec : forall p q : list X * list X, { p = q } + { p <> q }.
Proof.
decide equality; auto.
End bounded_dec.
End pcp_hand_dec.
Definition BPCP_input := list (list bool * list bool).
Definition BPCP_problem (R : BPCP_input) := exists l, R ⊳ l∕l.

Fact is_a_tail_dec (l t : list X) : { exists x, x++t = l } + { ~ exists x, x++t = l }.
Proof.
destruct (is_a_head_dec (rev l) (rev t)) as [ H | H ].
+
left; destruct H as (x & Hx).
exists (rev x).
apply f_equal with (f := @rev _) in Hx.
rewrite rev_app_distr in Hx.
do 2 rewrite rev_involutive in Hx; auto.
+
right; contradict H.
destruct H as (x & Hx); exists (rev x); subst.
apply rev_app_distr.
