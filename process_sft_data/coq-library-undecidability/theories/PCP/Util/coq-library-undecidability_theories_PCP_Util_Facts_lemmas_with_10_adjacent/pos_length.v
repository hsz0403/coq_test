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

Lemma is_cons_true_iff X (l : list X) : is_cons l = true <-> l <> [].
Proof.
Admitted.

Lemma fresh_spec' l a : a el l -> a < fresh l.
Proof.
induction l.
-
firstorder.
-
Admitted.

Lemma fresh_spec (a : nat) (l : list nat) : a el l -> fresh l <> a.
Proof.
intros H % fresh_spec'.
intros <-.
Admitted.

Lemma list_ind_ne A : A <> [] -> P A.
Proof using S B.
intros H.
destruct A.
congruence.
clear H.
revert x.
Admitted.

Lemma in_omap_iff X Y (f : X -> option Y) l y : y el omap f l <-> exists x, x el l /\ f x = Some y.
Proof.
induction l; cbn.
-
firstorder.
-
Admitted.

Lemma el_pos x A : x el A -> { n | pos x A = Some n }.
Proof.
induction A as [|y A IH]; cbn; intros H.
-
destruct H as [].
-
destruct (d x y) as [<-|H1].
+
now exists 0.
+
destruct IH as [n IH].
*
destruct H as [->|H]; tauto.
*
rewrite IH.
Admitted.

Lemma nthe_length A n : length A > n -> { x | nthe n A = Some x }.
Proof.
revert n.
induction A as [|y A IH]; cbn; intros n H.
-
exfalso.
lia.
-
destruct n as [|n]; cbn.
+
now exists y.
+
destruct (IH n) as [x H1].
lia.
Admitted.

Lemma pos_nthe x A n : pos x A = Some n -> nthe n A = Some x.
Proof.
revert n.
induction A as [|y A IH]; cbn; intros n.
-
intros [=].
-
destruct (d x y) as [<-|H1].
+
now intros [= <-].
+
destruct (pos x A) as [k|]; intros [= <-]; cbn.
Admitted.

Lemma nthe_app_l x n A B : nthe n A = Some x -> nthe n (A ++ B) = Some x.
Proof.
revert n.
induction A as [|y A IH]; cbn; intros k H.
-
destruct k; discriminate H.
-
destruct k as [|k]; cbn in *.
exact H.
Admitted.

Lemma pos_nth X d (x : X) l n def : pos d x l = Some n -> nth n l def = x.
Proof.
revert n; induction l; cbn; intros; try congruence.
Admitted.

Lemma cons_incl X (a : X) (A B : list X) : a :: A <<= B -> A <<= B.
Proof.
intros ? ? ?.
eapply H.
Admitted.

Lemma app_incl_l X (A B C : list X) : A ++ B <<= C -> A <<= C.
Proof.
intros H x Hx.
eapply H.
eapply in_app_iff.
Admitted.

Lemma app_incl_R X (A B C : list X) : A ++ B <<= C -> B <<= C.
Proof.
intros H x Hx.
eapply H.
eapply in_app_iff.
Admitted.

Lemma pos_length X d (x : X) l n : pos d x l = Some n -> n < | l |.
Proof.
revert n; induction l; cbn; intros; try congruence.
destruct (d x a).
-
inv H.
lia.
-
destruct (pos d x l) eqn:E; inv H; try lia.
specialize (IHl _ eq_refl).
lia.
