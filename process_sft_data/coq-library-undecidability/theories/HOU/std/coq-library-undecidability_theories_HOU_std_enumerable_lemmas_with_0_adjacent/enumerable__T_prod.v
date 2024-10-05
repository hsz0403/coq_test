Set Implicit Arguments.
Unset Strict Implicit.
Require Import List Arith Lia.
From Undecidability.HOU Require Import std.decidable std.lists.basics std.lists.advanced std.tactics.
Import ListNotations.
Set Default Proof Using "Type".
Notation "( A × B × .. × C )" := (list_prod .. (list_prod A B) .. C) (at level 0, left associativity).
Notation "[ s | p ∈ A ',' P ]" := (map (fun p => s) (filter (fun p => decb P) A)) (p pattern).
Notation "[ s | p ∈ A ]" := (map (fun p => s) A) (p pattern).
Notation "[ s 'where' H ':' P ]" := (match dec P with | left H => s :: nil | right _ => nil end) (H pattern).
Notation "[ s | p ∈ A 'where' H ':' P ]" := (flat_map (fun p => [s where H : P]) A) (p pattern, H pattern).
Notation "[ s | p ∈ A '&' q ∈ B ]" := (flat_map (fun q => map (fun p => s) A) B) (p pattern, q pattern).
Notation "[ s | p ∈ A '&' q ∈ B 'where' H ':' P ]" := (flat_map (fun q => map (fun p => [s where H : P]) A) B) (p pattern, q pattern).
Ltac in_collect a := eapply in_map_iff; exists a; split; [ eauto | match goal with [ |- _ ∈ filter _ _ ] => eapply filter_In; split; [ try (rewrite !in_prod_iff; repeat split) | repeat split; eauto ] | _ => try (rewrite !in_prod_iff; repeat split) end ].
Ltac in_app n := (match goal with | [ |- _ ∈ _ ++ _ ] => match n with | 0 => idtac | 1 => eapply in_app_iff; left | S ?n => eapply in_app_iff; right; in_app n end | [ |- _ ∈ _ :: _ ] => match n with 0 => idtac | 1 => left | S ?n => right; in_app n end end) || (repeat (try right; eapply in_app_iff; right)).
Ltac inv_collect := repeat (match goal with | [ H : ?x ∈ concat _ |- _ ] => eapply in_concat_iff in H as (? & ? & ?) | [ H : ?x ∈ map _ _ |- _ ] => let x := fresh "x" in eapply in_map_iff in H as (x & ? & ?) | [ x : ?A * ?B |- _ ] => destruct x; subst | [ H : ?x ∈ filter _ _ |- _ ] => let H' := fresh "H" in eapply filter_In in H as (? & H') | [ H : ?x ∈ list_prod _ _ |- _ ] => eapply in_prod_iff in H | [ H : _ ∈ _ ++ _ |- _ ] => try eapply in_app_iff in H as [] | [H : _ ∈ _ :: _ |- _ ] => destruct H end; intuition; subst).
Hint Extern 4 => match goal with |[ H: False |- _ ] => destruct H |[ H: true=false |- _ ] => discriminate H |[ H: false=true |- _ ] => discriminate H end : core.
Definition enumerable {X} (p : X -> Prop) := exists f, forall x, p x <-> exists n : nat, f n = Some x.
Definition enumerable__T X := exists f : nat -> option X, forall x, exists n, f n = Some x.
Definition cumulative {X} (L: nat -> list X) := forall n, exists A, L (S n) = L n ++ A.
Hint Extern 0 (cumulative _) => intros ?; cbn; eauto : core.
Definition enum {X} p (L: nat -> list X) := cumulative L /\ forall x, p x <-> exists m, x ∈ L m.
Section enumerable_enum.
Variable X : Type.
Variable p : X -> Prop.
Variables (e : nat -> option X).
Definition T_ (n : nat) : list X := match e n with Some x => [x] | None => [] end.
End enumerable_enum.
Class enumT X := { L_T : nat -> list X; cum_T : cumulative L_T ; el_T : forall x, exists m, x ∈ L_T m }.
Arguments L_T {_ _} _, _ {_} _.
Hint Immediate cum_T : core.
Instance enum_bool : enumT bool.
Proof.
exists (fun n => [true; false]).
-
eauto.
-
intros b; exists 1; destruct b; cbn; eauto.
Instance enumT_nat : enumT nat.
Proof.
exists (fix f n := match n with 0 => [0] | S n => f n ++ [S n] end).
-
intros ?; cbn; eauto.
-
intros n.
exists n.
destruct n; lauto.
Defined.
Section enumerable_prod.
Variable X Y : Type.
Section fixLs.
Variables (L_X : enumT X).
Variables (L_Y : enumT Y).
Fixpoint T_prod (n : nat) : list (X * Y) := match n with | 0 => [ (x,y) | (x,y) ∈ (L_T X 0 × L_T Y 0) ] | S n => T_prod n ++ [ (x,y) | (x,y) ∈ (L_T X n × L_T Y n) ] end.
End fixLs.
Global Instance prod_enumerable (LX : enumT X) (LY : enumT Y) : enumT (X * Y).
Proof.
exists (T_prod LX LY).
-
apply T_prod_cum.
-
apply T_prod_el.
Defined.
End enumerable_prod.
Definition R_nat_nat n : option (nat * nat) := nth_error (@L_T (nat * nat) _ n) n.
Section enum_enumerable.
Context X L p { enum_X : @enum X p L }.
Definition ofNat n := match R_nat_nat n with Some (n, m) => nth (L m) n | None => None end.
End enum_enumerable.
Section enumerable_list.
Variable X : Type.
Section fixL.
Variables (LX : enumT X).
Fixpoint T_list (n : nat) : list (list X) := match n with | 0 => [ [] ] | S n => T_list n ++ [ x :: L | (x,L) ∈ (L_T X n × T_list n) ] end.
End fixL.
Global Instance enumerable_list (LX : enumT X) : enumT (list X).
Proof.
exists (T_list LX).
apply T_list_cum.
apply T_list_el.
End enumerable_list.
Require Import ConstructiveEpsilon.
Section Choice.
Definition mu_enum X (p : X -> Prop) f : Dis X -> (forall x : X, p x <-> (exists n : nat, f n = Some x)) -> ex p -> sig p.
Proof.
intros E Hf H.
assert (exists n x, f n = Some x).
destruct H; rewrite Hf in H; firstorder.
eapply constructive_indefinite_ground_description with (f := id) (g := id) in H0 as (? & ?); eauto.
-
destruct (f x) eqn:E2.
exists x0.
destruct e.
inv H0.
eapply Hf.
eauto.
exfalso.
destruct e.
inv H0.
-
intros.
destruct (f x).
left.
eauto.
right.
intros [].
inv H1.
End Choice.

Lemma enumerable__T_prod X Y : enumerable__T X -> enumerable__T Y -> enumerable__T (X * Y).
Proof.
intros [LX] % enum_enumT [LY] % enum_enumT.
eapply enum_enumT.
econstructor.
exact _.
