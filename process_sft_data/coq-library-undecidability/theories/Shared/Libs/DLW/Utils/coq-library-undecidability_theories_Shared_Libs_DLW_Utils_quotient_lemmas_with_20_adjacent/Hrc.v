Require Import List Arith Lia Permutation Relations Bool Eqdep_dec.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_nat.
Set Implicit Arguments.
Definition nat_enum_cls X (R : X -> X -> Prop) := { f : nat -> option X | forall x, exists y n, f n = Some y /\ R y x }.
Notation dec := ((fun X Y (R : X -> Y -> Prop) => forall x y, { R x y } + { R x y -> False }) _ _).
Definition quotient X (R : X -> X -> Prop) Y := { cls : X -> Y & { rpr : Y -> X | (forall y, cls (rpr y) = y) /\ (forall x1 x2, R x1 x2 <-> cls x1 = cls x2) } }.
Section ep_quotient.
Variable (X : Type) (R : X -> X -> Prop) (f : nat -> option X) (Hf : forall x, exists y n, f n = Some y /\ R y x).
Hypothesis HR1 : equiv _ R.
Hypothesis HR2 : dec R.
Let T n m := match f n, f m with | Some x, Some y => R x y | None , None => True | _ , _ => False end.
Let HT1 : equiv _ T.
Proof.
msplit 2.
+
intros x; red; destruct (f x); auto; apply (proj1 HR1).
+
intros x y z; unfold T.
destruct (f x); destruct (f y); destruct (f z); try tauto; apply HR1.
+
intros x y; unfold T.
destruct (f x); destruct (f y); try tauto; apply HR1.
Infix "≈" := T (at level 70, no associativity).
Let is_repr x n := match f n with | Some r => R r x | None => False end.
Let is_repr_trans x1 x2 n : R x1 x2 -> is_repr x1 n -> is_repr x2 n.
Proof.
intros H1 H2; revert H2 H1.
unfold is_repr; destruct (f n); auto.
apply HR1.
Let is_repr_dec : dec is_repr.
Proof.
intros x n.
unfold is_repr.
destruct (f n).
+
apply HR2.
+
tauto.
Let is_repr_exists x : ex (is_repr x).
Proof.
destruct (Hf x) as (y & n & H1 & H2).
exists n; red; rewrite H1; auto.
Let is_min_repr x n := is_repr x n /\ forall m, is_repr x m -> n <= m.
Let is_min_repr_inj x n1 n2 : is_min_repr x n1 -> is_min_repr x n2 -> n1 = n2.
Proof.
intros (H1 & H2) (H3 & H4).
apply Nat.le_antisymm; auto.
Let is_min_repr_involutive x n : is_min_repr x n -> match f n with | Some y => is_min_repr y n | None => False end.
Proof.
intros (H1 & H2); unfold is_min_repr, is_repr in *.
destruct (f n) as [ y | ]; try tauto.
split.
+
apply (proj1 HR1).
+
intros m; specialize (H2 m).
destruct (f m) as [ k | ]; try tauto.
intros H3; apply H2, (proj1 (proj2 HR1)) with (1 := H3); auto.
Let find_min_repr x : sig (is_min_repr x).
Proof.
destruct min_dec with (P := is_repr x) as (r & H1 & H2).
+
intro; apply is_repr_dec.
+
apply is_repr_exists.
+
exists r; split; auto.
Let is_min_repr_dec : dec is_min_repr.
Proof.
unfold is_min_repr, is_repr.
intros x n.
destruct (f n) as [ y | ].
2: right; tauto.
destruct (HR2 y x) as [ H1 | H1 ].
2: right; tauto.
destruct bounded_search with (m := n) (P := fun m => match f m with Some r => R r x | None => False end) as [ (p & H2 & H3) | H ].
+
intros m _; destruct (is_repr_dec x m); auto.
+
case_eq (f p).
*
intros r Hr.
right; intros (G1 & G2).
specialize (G2 p).
rewrite Hr in G2, H3.
specialize (G2 H3); lia.
*
intros Hr; rewrite Hr in H3; tauto.
+
left; split; auto.
intros m Hm.
destruct (le_lt_dec n m) as [ | C ]; auto.
exfalso; specialize (H _ C).
destruct (f m) as [ z | ]; tauto.
Let P n := match f n with | Some x => if is_min_repr_dec x n then true else false | None => false end.
Let P_spec n : P n = true <-> exists x, f n = Some x /\ is_min_repr x n.
Proof.
unfold P.
destruct (f n) as [ x | ].
+
destruct (is_min_repr_dec x n) as [ | C ]; split; try tauto.
*
exists x; auto.
*
discriminate.
*
intros (y & Hy & ?).
destruct C; inversion Hy; auto.
+
split; try discriminate.
intros (? & ? & _); discriminate.
Let Y := sig (fun x => P x = true).
Let pi1_inj : forall x y : Y, proj1_sig x = proj1_sig y -> x = y.
Proof.
intros (x & H1) (y & H2); simpl; intros; subst; f_equal.
apply UIP_dec, bool_dec.
Let Y_discrete : dec (@eq Y).
Proof.
intros (x & Hx) (y & Hy).
destruct (eq_nat_dec x y) as [ | H ].
+
left; apply pi1_inj; simpl; auto.
+
right; contradict H; inversion H; auto.
Let is_min_repr_P n x : is_min_repr x n -> P n = true.
Proof.
intros H1.
apply P_spec; revert H1.
unfold is_min_repr, is_repr.
case_eq (f n).
+
intros y Hy (H1 & H2).
exists y; msplit 2; auto.
*
apply (proj1 HR1).
*
intros m; specialize (H2 m).
destruct (f m) as [ z | ]; auto.
intros H; apply H2, (proj1 (proj2 HR1) _ y); auto.
+
intros _ ([] & _).
Let cls (x : X) : Y.
Proof.
destruct (find_min_repr x) as (n & Hn).
exists n; apply is_min_repr_P with x; auto.
Defined.
Let P_to_X n : P n = true -> { k | f n = Some k }.
Proof.
intros H; rewrite P_spec in H.
case_eq (f n).
+
intros k _; exists k; auto.
+
intros Hn; exfalso; revert Hn.
destruct H as (x & -> & _); discriminate.
Let rpr (y : Y) := proj1_sig (P_to_X _ (proj2_sig y)).
Let Hrpr y : f (proj1_sig y) = Some (rpr y).
Proof.
apply (proj2_sig (P_to_X _ (proj2_sig y))).
Let Hcr : forall y, cls (rpr y) = y.
Proof.
intros (n & Hn); simpl.
unfold rpr; simpl.
apply pi1_inj; simpl; unfold cls.
case (find_min_repr (proj1_sig (P_to_X n Hn))).
intros m Hm; simpl.
generalize Hn; rewrite P_spec; intros (y & G1 & G2).
destruct (P_to_X n Hn) as (z & Hz); simpl in Hm.
rewrite Hz in G1; inversion G1; subst z.
revert Hm G2; apply is_min_repr_inj.
Let Hrc x1 x2 : R x1 x2 <-> cls x1 = cls x2.
Proof.
split.
+
intros H; apply pi1_inj.
unfold cls.
case (find_min_repr x1); intros y1 (G1 & G2); simpl.
case (find_min_repr x2); intros y2 (G3 & G4); simpl.
apply Nat.le_antisymm.
*
apply G2; revert G3.
apply is_repr_trans, (proj2 (proj2 HR1)); auto.
*
apply G4; revert G1.
apply is_repr_trans; auto.
+
unfold cls.
case (find_min_repr x1); intros y1 G1; simpl.
case (find_min_repr x2); intros y2 G2; simpl.
intros H; inversion H; subst y2; clear H.
apply proj1 in G1; apply proj1 in G2.
revert G1 G2; unfold is_repr.
destruct (f y1); try tauto; intros H.
apply HR1; revert H; apply HR1.
Local Fact enum_quotient_rec : { Y : Type & { _ : dec (@eq Y) & quotient R Y } }.
Proof.
exists Y, Y_discrete, cls, rpr; split; auto.
End ep_quotient.
Fact quotient_is_enum X R Y : nat_enum_cls R -> @quotient X R Y -> nat_enum_cls (@eq Y).
Proof.
intros (f & Hf) (c & r & H1 & H2).
exists (fun n => match f n with Some x => Some (c x) | None => None end).
intros y.
destruct (Hf (r y)) as (z & n & H3 & H4).
exists (c z), n; rewrite H3; split; auto.
rewrite <- (H1 y); apply H2; auto.

Let HT1 : equiv _ T.
Proof.
msplit 2.
+
intros x; red; destruct (f x); auto; apply (proj1 HR1).
+
intros x y z; unfold T.
destruct (f x); destruct (f y); destruct (f z); try tauto; apply HR1.
+
intros x y; unfold T.
Admitted.

Let is_repr_trans x1 x2 n : R x1 x2 -> is_repr x1 n -> is_repr x2 n.
Proof.
intros H1 H2; revert H2 H1.
unfold is_repr; destruct (f n); auto.
Admitted.

Let is_repr_dec : dec is_repr.
Proof.
intros x n.
unfold is_repr.
destruct (f n).
+
apply HR2.
+
Admitted.

Let is_repr_exists x : ex (is_repr x).
Proof.
destruct (Hf x) as (y & n & H1 & H2).
Admitted.

Let is_min_repr_inj x n1 n2 : is_min_repr x n1 -> is_min_repr x n2 -> n1 = n2.
Proof.
intros (H1 & H2) (H3 & H4).
Admitted.

Let is_min_repr_involutive x n : is_min_repr x n -> match f n with | Some y => is_min_repr y n | None => False end.
Proof.
intros (H1 & H2); unfold is_min_repr, is_repr in *.
destruct (f n) as [ y | ]; try tauto.
split.
+
apply (proj1 HR1).
+
intros m; specialize (H2 m).
destruct (f m) as [ k | ]; try tauto.
Admitted.

Let find_min_repr x : sig (is_min_repr x).
Proof.
destruct min_dec with (P := is_repr x) as (r & H1 & H2).
+
intro; apply is_repr_dec.
+
apply is_repr_exists.
+
Admitted.

Let is_min_repr_dec : dec is_min_repr.
Proof.
unfold is_min_repr, is_repr.
intros x n.
destruct (f n) as [ y | ].
2: right; tauto.
destruct (HR2 y x) as [ H1 | H1 ].
2: right; tauto.
destruct bounded_search with (m := n) (P := fun m => match f m with Some r => R r x | None => False end) as [ (p & H2 & H3) | H ].
+
intros m _; destruct (is_repr_dec x m); auto.
+
case_eq (f p).
*
intros r Hr.
right; intros (G1 & G2).
specialize (G2 p).
rewrite Hr in G2, H3.
specialize (G2 H3); lia.
*
intros Hr; rewrite Hr in H3; tauto.
+
left; split; auto.
intros m Hm.
destruct (le_lt_dec n m) as [ | C ]; auto.
exfalso; specialize (H _ C).
Admitted.

Let P_spec n : P n = true <-> exists x, f n = Some x /\ is_min_repr x n.
Proof.
unfold P.
destruct (f n) as [ x | ].
+
destruct (is_min_repr_dec x n) as [ | C ]; split; try tauto.
*
exists x; auto.
*
discriminate.
*
intros (y & Hy & ?).
destruct C; inversion Hy; auto.
+
split; try discriminate.
Admitted.

Let pi1_inj : forall x y : Y, proj1_sig x = proj1_sig y -> x = y.
Proof.
intros (x & H1) (y & H2); simpl; intros; subst; f_equal.
Admitted.

Let Y_discrete : dec (@eq Y).
Proof.
intros (x & Hx) (y & Hy).
destruct (eq_nat_dec x y) as [ | H ].
+
left; apply pi1_inj; simpl; auto.
+
Admitted.

Let is_min_repr_P n x : is_min_repr x n -> P n = true.
Proof.
intros H1.
apply P_spec; revert H1.
unfold is_min_repr, is_repr.
case_eq (f n).
+
intros y Hy (H1 & H2).
exists y; msplit 2; auto.
*
apply (proj1 HR1).
*
intros m; specialize (H2 m).
destruct (f m) as [ z | ]; auto.
intros H; apply H2, (proj1 (proj2 HR1) _ y); auto.
+
Admitted.

Let cls (x : X) : Y.
Proof.
destruct (find_min_repr x) as (n & Hn).
Admitted.

Let P_to_X n : P n = true -> { k | f n = Some k }.
Proof.
intros H; rewrite P_spec in H.
case_eq (f n).
+
intros k _; exists k; auto.
+
intros Hn; exfalso; revert Hn.
Admitted.

Let Hrpr y : f (proj1_sig y) = Some (rpr y).
Proof.
Admitted.

Let Hcr : forall y, cls (rpr y) = y.
Proof.
intros (n & Hn); simpl.
unfold rpr; simpl.
apply pi1_inj; simpl; unfold cls.
case (find_min_repr (proj1_sig (P_to_X n Hn))).
intros m Hm; simpl.
generalize Hn; rewrite P_spec; intros (y & G1 & G2).
destruct (P_to_X n Hn) as (z & Hz); simpl in Hm.
rewrite Hz in G1; inversion G1; subst z.
Admitted.

Theorem enum_quotient X R : nat_enum_cls R -> equiv X R -> dec R -> { Y : Type & { _ : dec (@eq Y) & quotient R Y } }.
Proof.
intros (f & Hf) H1 H2.
Admitted.

Fact quotient_is_enum X R Y : nat_enum_cls R -> @quotient X R Y -> nat_enum_cls (@eq Y).
Proof.
intros (f & Hf) (c & r & H1 & H2).
exists (fun n => match f n with Some x => Some (c x) | None => None end).
intros y.
destruct (Hf (r y)) as (z & n & H3 & H4).
exists (c z), n; rewrite H3; split; auto.
Admitted.

Let Hrc x1 x2 : R x1 x2 <-> cls x1 = cls x2.
Proof.
split.
+
intros H; apply pi1_inj.
unfold cls.
case (find_min_repr x1); intros y1 (G1 & G2); simpl.
case (find_min_repr x2); intros y2 (G3 & G4); simpl.
apply Nat.le_antisymm.
*
apply G2; revert G3.
apply is_repr_trans, (proj2 (proj2 HR1)); auto.
*
apply G4; revert G1.
apply is_repr_trans; auto.
+
unfold cls.
case (find_min_repr x1); intros y1 G1; simpl.
case (find_min_repr x2); intros y2 G2; simpl.
intros H; inversion H; subst y2; clear H.
apply proj1 in G1; apply proj1 in G2.
revert G1 G2; unfold is_repr.
destruct (f y1); try tauto; intros H.
apply HR1; revert H; apply HR1.
