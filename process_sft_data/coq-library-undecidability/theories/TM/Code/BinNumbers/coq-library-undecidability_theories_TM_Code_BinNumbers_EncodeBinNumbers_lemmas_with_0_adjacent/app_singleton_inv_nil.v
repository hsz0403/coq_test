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

Lemma app_singleton_inv_nil (X : Type) (xs : list X) (x y : X) : xs ++ [x] = [y] -> xs = nil /\ x = y.
Proof.
destruct xs as [ | x' xs']; cbn in *; intros H; inv H; auto.
exfalso.
symmetry in H2.
now apply app_cons_not_nil in H2.
