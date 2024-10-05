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

Lemma in_concat_iff A l (a:A) : a ∈ concat l <-> exists l', a ∈ l' /\ l' ∈ l.
Proof.
induction l; cbn.
-
intuition.
now destruct H.
-
rewrite in_app_iff, IHl.
firstorder subst.
Admitted.

Lemma enumerable_enumerable_T X : enumerable (fun _ : X => True) <-> enumerable__T X.
Proof.
split.
-
intros [e He].
exists e.
intros x.
now eapply He.
-
intros [c Hc].
exists c.
intros x.
Admitted.

Lemma cum_ge {X} (L: nat -> list X) n m : cumulative L -> m >= n -> exists A, L m = L n ++ A.
Proof.
induction 2 as [|m _ IH].
-
exists nil.
now rewrite app_nil_r.
-
destruct (H m) as (A&->), IH as [B ->].
exists (B ++ A).
Admitted.

Lemma cum_ge' {X} (L: nat -> list X) x n m : cumulative L -> x ∈ L n -> m >= n -> x ∈ L m.
Proof.
intros ? H [A ->] % (cum_ge (L := L)).
apply in_app_iff.
eauto.
Admitted.

Lemma count_enum' : exists L : nat -> list X, forall x, (exists n, e n = Some x) <-> (exists n, x ∈ L n).
Proof.
exists T_.
split; intros [n H].
-
exists n.
unfold T_.
rewrite H.
lauto.
-
unfold T_ in *.
destruct (e n) eqn:E.
inv H.
eauto.
inv H0.
Admitted.

Lemma enum_to_cumulative X (p : X -> Prop) L : (forall x, p x <-> exists m : nat, x ∈ L m) -> exists L, enum p L.
Proof.
intros H.
exists (fix L' n := match n with 0 => [] | S n => L' n ++ L n end).
split.
-
eauto.
-
intros x.
rewrite H.
split; intros [m Hm].
+
exists (S m).
intuition.
+
induction m; try now inv Hm.
Admitted.

Instance enum_bool : enumT bool.
Proof.
exists (fun n => [true; false]).
-
eauto.
-
Admitted.

Lemma count_bool : enumerable__T bool.
Proof.
exists (fun n => match n with 0 => Some true | _ => Some false end).
intros [].
now exists 0.
Admitted.

Instance enumT_nat : enumT nat.
Proof.
exists (fix f n := match n with 0 => [0] | S n => f n ++ [S n] end).
-
intros ?; cbn; eauto.
-
intros n.
exists n.
Admitted.

Lemma T_nat_in n m : m <= n -> m ∈ L_T nat n.
Proof.
induction 1.
-
destruct m; cbn.
tauto.
apply in_app_iff.
cbn.
tauto.
-
cbn.
apply in_app_iff.
Admitted.

Lemma T_nat_length n : length (L_T nat n) = S n.
Proof.
induction n; cbn; try rewrite app_length.
lia.
cbn in *.
Admitted.

Lemma T_prod_cum : cumulative T_prod.
Proof.
Admitted.

Lemma T_prod_el LX LY (a : X * Y) : exists n, a ∈ T_prod LX LY n.
Proof.
destruct a.
destruct (el_T x) as [m1], (el_T y) as [m2].
exists (1 + m1 + m2).
cbn.
in_app 2.
Admitted.

Lemma C_exhaustive n m : (n,m) ∈ L_T (1 + n + m).
Proof.
cbn.
in_app 2.
Admitted.

Lemma C_longenough n : length (L_T (nat * nat) n) > n.
Proof.
induction n; cbn.
-
lia.
-
rewrite app_length, map_length, prod_length, T_nat_length.
cbn in *.
remember (n + n * S n) as k.
Admitted.

Lemma pairs_retract : forall p, exists n, R_nat_nat n = Some p.
Proof.
intros [n m].
unfold R_nat_nat.
destruct(find (n,m) (L_T (1 + n + m))) as [ k | ] eqn:A.
exists k.
destruct (nth (L_T k) k) eqn:B.
-
eapply find_Some in A.
destruct (le_lt_dec k (1 + n + m)) as [D | ?].
+
destruct (cum_ge (@cum_T (nat * nat) _) D) as [B' HB].
rewrite HB in A.
erewrite (nth_error_app1 _ _), B in A.
now injection A.
eapply nth_error_Some_lt; eauto.
+
assert (1 + n + m <= k) as D by lia.
destruct (cum_ge (@cum_T (nat * nat) _) D) as [B' HB].
rewrite HB in B.
erewrite (nth_error_app1 _ _), A in B.
now injection B.
eapply nth_error_Some_lt; eauto.
-
exfalso.
edestruct nth_error_lt_Some.
2:{
rewrite H in B.
inv B.
}
eapply C_longenough.
-
exfalso.
destruct (find_in _ _ (C_exhaustive n m)) as [k H].
Admitted.

Lemma enumerable_nat_nat : enumerable__T (nat * nat).
Proof.
exists R_nat_nat.
Admitted.

Lemma enum_count : enumerable p.
Proof using enum_X L.
exists ofNat.
unfold R_nat_nat.
destruct enum_X as [CX HX].
intros.
rewrite HX.
-
split; intros [n].
+
eapply In_nth_error in H as [m].
destruct (pairs_retract (m, n)) as [k].
exists k.
unfold ofNat.
now rewrite H0.
+
unfold ofNat in *.
destruct R_nat_nat as [ [] | ].
eapply nth_error_In in H.
eauto.
Admitted.

Lemma enumerable_enum X p : (exists L, enum p L) <-> @enumerable X p.
Proof.
split.
-
intros [L].
eapply enum_count; eauto.
-
intros [f].
destruct count_enum' with (e := f) as (L & ?).
eapply enum_to_cumulative.
intros.
Admitted.

Lemma count_nat : enumerable__T nat.
Proof.
exists Some.
intros n.
now exists n.
