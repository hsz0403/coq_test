From Undecidability Require Import TM.Util.Prelim Code.
From Undecidability Require Import ArithPrelim.
From Undecidability.Shared.Libs.PSL Require Export Bijection.
Require Export BinNums.
Inductive sigPos : Type := | sigPos_xI : sigPos | sigPos_xO : sigPos | sigPos_xH : sigPos.
Global Instance sigPos_eq : eq_dec sigPos.
Proof.
unfold dec.
decide equality.
Defined.
Global Instance sigPos_fin : finTypeC (EqType sigPos).
Proof.
split with (enum := [sigPos_xI; sigPos_xO; sigPos_xH]).
intros [ | | ]; cbn; reflexivity.
Fixpoint encode_pos (x : positive) : list sigPos := match x with | xI x' => encode_pos x' ++ [sigPos_xI] | xO x' => encode_pos x' ++ [sigPos_xO] | xH => [sigPos_xH] end.
Global Instance Encode_positive : codable sigPos positive := {| encode := encode_pos; |}.
Notation sigN := (sigOption sigPos).
Definition N_to_optionPos : BinNums.N -> option positive := fun n => match n with | N0 => None | Npos p => Some p end.
Instance Encode_N : codable sigN BinNums.N := {| encode n := encode (N_to_optionPos n); |}.
Definition Encode_N_size (n : N) : nat := match n with | N0 => 1 | Npos p => S (Pos.size_nat p) end.

Lemma Encode_positive_hasSize x : size x = Pos.size_nat x.
Proof.
Admitted.

Corollary Encode_positive_eq_nil x : Encode_positive x <> nil.
Proof.
intros H % length_zero_iff_nil.
setoid_rewrite Encode_positive_hasSize in H.
Admitted.

Lemma app_singleton_inv (X : Type) (xs ys : list X) (x y : X) : xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y.
Proof.
revert ys.
induction xs as [ | x' xs' IH]; intros; cbn in *.
-
destruct ys as [ | y']; cbn in *; inv H; auto.
exfalso.
now apply app_cons_not_nil in H2.
-
destruct ys as [ | y']; cbn in *; inv H; auto.
+
exfalso.
symmetry in H2.
now apply app_cons_not_nil in H2.
+
Admitted.

Lemma Encode_positive_injective : injective encode_pos.
Proof.
cbn.
hnf.
intros n1.
induction n1; intros n2 H; cbn in *.
-
destruct n2; cbn in *; try congruence.
+
apply app_singleton_inv in H as (H1&H1'); inv H1'; auto using f_equal.
+
apply app_singleton_inv in H as (H1&H1'); inv H1'; auto using f_equal.
+
exfalso.
apply app_singleton_inv_nil in H as (H&H'); inv H'.
-
destruct n2; cbn in *; try congruence.
+
apply app_singleton_inv in H as (H1&H1'); inv H1'; auto using f_equal.
+
apply app_singleton_inv in H as (H1&H1'); inv H1'; auto using f_equal.
+
exfalso.
apply app_singleton_inv_nil in H as (H&H'); inv H'.
-
destruct n2; cbn in *; try congruence.
+
symmetry in H.
apply app_singleton_inv_nil in H as (H1&H1'); inv H1'; auto using f_equal.
+
symmetry in H.
Admitted.

Lemma Encode_positive_startsWith_xH (x : positive) : exists str', encode_pos x = sigPos_xH :: str'.
Proof.
induction x; cbn; eauto.
-
destruct IHx.
eexists (_ ++ _); cbn.
setoid_rewrite H; cbn; eauto.
-
destruct IHx.
eexists (_ ++ _); cbn.
Admitted.

Lemma Encode_N_hasSize (n : N) : size n = Encode_N_size n.
Proof.
destruct n; cbn; auto.
simpl_list.
f_equal.
Admitted.

Lemma app_singleton_inv_nil (X : Type) (xs : list X) (x y : X) : xs ++ [x] = [y] -> xs = nil /\ x = y.
Proof.
destruct xs as [ | x' xs']; cbn in *; intros H; inv H; auto.
exfalso.
symmetry in H2.
now apply app_cons_not_nil in H2.
