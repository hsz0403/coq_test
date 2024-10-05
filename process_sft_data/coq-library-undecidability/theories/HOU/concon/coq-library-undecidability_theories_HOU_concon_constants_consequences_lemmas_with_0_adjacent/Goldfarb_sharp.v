Require Import List Arith Lia Morphisms Setoid.
From Undecidability.HOU Require Import calculus.calculus.
From Undecidability.HOU Require Import unification.higher_order_unification unification.nth_order_unification concon.conservativity_constants concon.conservativity concon.constants.
Import ListNotations.
From Undecidability.HOU Require Import second_order.diophantine_equations second_order.goldfarb.reduction.
Definition gonly : Const := {| const_type := option False; ctype := fun o => match o with | None => alpha → alpha → alpha | Some f => match f with end end |}.
Program Instance RE_ag_gonly : retract gonly ag := {| I := fun _ => None; R := fun x => match x with None => Some None | _ => None end |}.
Next Obligation.
now destruct x as [[]|].
Definition cfree : Const := {| const_type := False; ctype := fun f => match f with end |}.
Program Instance RE_cfree X : retract cfree X := {| I := fun f => match f with end; R := fun x => None |}.

Lemma Goldfarb_sharp (C: Const) (re: retract gonly C): ctype C (I None) = alpha → alpha → alpha -> OU 2 gonly ⪯ OU 2 C.
Proof.
intros.
eapply unification_constants_monotone; eauto.
intros [[]|]; cbn; eauto.
