Require Import List Lia.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "| A |" := (length A) (at level 65).
Ltac inv H := inversion H; subst; try clear H.
Definition is_cons X (l : list X) := match l with | [] => false | _ => true end.
Fixpoint fresh (l : list nat) := match l with | [] => 0 | x :: l => S x + fresh l end.
Section neList.
Variable X : Type.
Variable P : list X -> Prop.
Hypothesis B : (forall x : X, P [x]).
Hypothesis S : (forall x A, P A -> P (x :: A)).
End neList.
Fixpoint omap X Y (f : X -> option Y) l := match l with | nil => nil | x :: l => match f x with Some y => y :: omap f l | None => omap f l end end.
Section Positions.
Variables (X: Type) (d: forall x y : X, {x = y} + {x <> y}).
Implicit Types (x y: X) (A B : list X).
Fixpoint pos x A : option nat := match A with | nil => None | y :: A' => if d x y then Some 0 else match pos x A' with | Some n => Some (S n) | None => None end end.
Notation nthe n A := (nth_error A n).
End Positions.
Notation nthe n A := (nth_error A n).

Lemma in_omap_iff X Y (f : X -> option Y) l y : y el omap f l <-> exists x, x el l /\ f x = Some y.
Proof.
induction l; cbn.
-
firstorder.
-
destruct (f a) eqn:E; firstorder (subst; firstorder congruence).
