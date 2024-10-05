Require Import List Lia.
Import ListNotations.
Require Import Undecidability.CounterMachines.CM2.
Require Import Undecidability.CounterMachines.Util.Nat_facts.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma haltingP {cm c} : halting cm c <-> length cm <= state c.
Proof.
move:c => [p a b].
rewrite /halting /=.
move Hoi: (nth_error cm p) => oi.
case: oi Hoi; last by move=> /nth_error_None.
move=> [] x => [|?] Hp /=.
-
constructor; [by case; lia | by rewrite -nth_error_None Hp].
-
move: x a b Hp => [] [|?] [|?]; (constructor; [by case; lia | by rewrite -nth_error_None Hp]).
