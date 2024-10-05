Require Import List Arith Lia Max.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability Require Import Shared.Libs.DLW.Utils.utils H10.Dio.dio_logic H10.Dio.dio_elem.
From Undecidability Require Import H10.FRACTRAN_DIO FRACTRAN.FRACTRAN.
Require Import Undecidability.DiophantineConstraints.H10C.
Set Implicit Arguments.
Section dc_list_h10c.
Variable (ν : nat -> nat).
Let even n := 2*n+2.
Let odd n := 2*n+1.
Let h10c_nat n := match n with | 0 => h10c_plus (even 0) (even 0) (even 0) | S n => h10c_plus (even n) 0 (even (S n)) end.
Let dc_h10c (c : dio_constraint) := let (x,c) := c in match c with | dee_nat n => h10c_plus (even n) (even 0) (odd x) | dee_var y => h10c_plus (odd y) (even 0) (odd x) | dee_par p => h10c_plus (even (ν p)) (even 0) (odd x) | dee_comp do_add y z => h10c_plus (odd y) (odd z) (odd x) | dee_comp do_mul y z => h10c_mult (odd y) (odd z) (odd x) end.
Let dee_const c := match c with | dee_nat n => n::nil | dee_par p => ν p::nil | _ => nil end.
Section dc_h10c_equiv.
Variable (φ Ψ : nat -> nat) (Hpsy_0 : Ψ 0 = 1) (Hpsy_odd : forall n, Ψ (odd n) = φ n).
Local Lemma dc_h10c_equiv c : (forall n, In n (0::dee_const (snd c)) -> Ψ (even n) = n) -> dc_eval φ ν c <-> h10c_sem (dc_h10c c) Ψ.
Proof.
destruct c as (x,[ n | y | p | [] y z ]); unfold dc_eval; simpl; intros H.
+
do 2 (rewrite H; auto); rewrite Hpsy_odd; lia.
+
rewrite H; auto; do 2 rewrite Hpsy_odd; lia.
+
do 2 (rewrite H; auto); rewrite Hpsy_odd; lia.
+
do 3 rewrite Hpsy_odd; lia.
+
do 3 rewrite Hpsy_odd; lia.
End dc_h10c_equiv.
Let Fixpoint dc_max (l : list dio_constraint) := match l with | nil => 0 | (_,dee_nat n)::l => max n (dc_max l) | (_,dee_par p)::l => max (ν p) (dc_max l) | _::l => dc_max l end.
Let dc_list_const l := list_an 0 (1+dc_max l).
Let dc_list_const_prop c l : In c l -> incl (0::dee_const (snd c)) (dc_list_const l).
Proof.
intros Hc x [ Hx | Hx ]; apply list_an_spec.
+
subst; lia.
+
split; try lia; apply le_n_S.
revert x Hx; rewrite <- Forall_forall.
revert c Hc; rewrite <- Forall_forall.
induction l as [ | (x,c) l IHl ].
-
constructor.
-
constructor.
*
destruct c as [ n | y | p | [] y z ]; simpl; repeat constructor; apply le_max_l.
*
revert IHl; apply Forall_impl.
intros y _; apply Forall_impl.
intros z _ Hz.
apply le_trans with (1 := Hz).
simpl; clear y z Hz.
destruct c as [ n | y | p | [] y z ]; auto; apply le_max_r.
Definition dc_list_h10c l := h10c_one 0 :: map h10c_nat (dc_list_const l) ++ map dc_h10c l.
End dc_list_h10c.
Section DIO_ELEM_H10C_SAT.
Let f (P : DIO_ELEM_PROBLEM) : list h10c := let (l,ν) := P in dc_list_h10c ν l.
End DIO_ELEM_H10C_SAT.
Check DIO_ELEM_H10C_SAT.
Check FRACTRAN_HALTING_DIO_LOGIC_SAT.
Check DIO_LOGIC_ELEM_SAT.

Let dc_list_const_prop c l : In c l -> incl (0::dee_const (snd c)) (dc_list_const l).
Proof.
intros Hc x [ Hx | Hx ]; apply list_an_spec.
+
subst; lia.
+
split; try lia; apply le_n_S.
revert x Hx; rewrite <- Forall_forall.
revert c Hc; rewrite <- Forall_forall.
induction l as [ | (x,c) l IHl ].
-
constructor.
-
constructor.
*
destruct c as [ n | y | p | [] y z ]; simpl; repeat constructor; apply le_max_l.
*
revert IHl; apply Forall_impl.
intros y _; apply Forall_impl.
intros z _ Hz.
apply le_trans with (1 := Hz).
simpl; clear y z Hz.
destruct c as [ n | y | p | [] y z ]; auto; apply le_max_r.
