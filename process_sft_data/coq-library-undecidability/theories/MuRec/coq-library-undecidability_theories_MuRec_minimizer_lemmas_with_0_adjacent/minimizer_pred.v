Require Import Arith Lia.
Set Implicit Arguments.
Set Default Proof Using "Type".
Section nat_rev_ind.
Variables (P : nat -> Prop) (HP : forall n, P (S n) -> P n).
End nat_rev_ind.
Section nat_rev_ind'.
Variables (P : nat -> Prop) (k : nat) (HP : forall n, n < k -> P (S n) -> P n).
End nat_rev_ind'.
Section minimizer_pred.
Variable (P : nat -> Prop) (HP : forall p: { n | P n \/ ~ P n }, { P (proj1_sig p) } + { ~ P (proj1_sig p) }).
Definition minimizer n := P n /\ forall i, i < n -> ~ P i.
Inductive bar n : Prop := | in_bar_0 : P n -> bar n | in_bar_1 : ~ P n -> bar (S n) -> bar n.
Let bar_ex n : bar n -> P n \/ ~ P n.
Proof.
induction 1; auto.
Let loop : forall n, bar n -> { k | P k /\ forall i, n <= i < k -> ~ P i }.
Proof.
refine (fix loop n Hn { struct Hn } := match HP (exist _ n (bar_ex Hn)) with | left H => exist _ n _ | right H => match loop (S n) _ with | exist _ k Hk => exist _ k _ end end).
*
split; auto; intros; lia.
*
destruct Hn; [ destruct H | ]; assumption.
*
destruct Hk as (H1 & H2).
split; trivial; intros i Hi.
destruct (eq_nat_dec i n).
-
subst; trivial.
-
apply H2; lia.
Hypothesis Hmin : ex minimizer.
Let bar_0 : bar 0.
Proof.
destruct Hmin as (k & H1 & H2).
apply in_bar_0 in H1.
clear HP.
revert H1.
apply nat_rev_ind' with (k := k).
intros i H3.
apply in_bar_1, H2; trivial.
lia.
Definition minimizer_pred : sig minimizer.
Proof using Hmin loop.
destruct (loop bar_0) as (k & H1 & H2).
exists k; split; auto.
intros; apply H2; lia.
Defined.
End minimizer_pred.

Definition minimizer_pred : sig minimizer.
Proof using Hmin loop.
destruct (loop bar_0) as (k & H1 & H2).
exists k; split; auto.
intros; apply H2; lia.
