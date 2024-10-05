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
apply app_singleton_inv_nil in H as (H1&H1'); inv H1'; auto using f_equal.
