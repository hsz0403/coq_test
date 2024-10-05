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

Theorem dc_list_h10c_spec l : (exists φ, Forall (dc_eval φ ν) l) <-> (exists Ψ, Forall (fun c => h10c_sem c Ψ) (dc_list_h10c l)).
Proof.
split.
+
intros (phi & Hphi).
set (psy n := match div2 n with | (0 , false) => 1 | (S n, false) => n | (n , true) => phi n end).
assert (Hpsy_0 : psy 0 = 1) by reflexivity.
assert (Hpsy_even : forall n, psy (even n) = n).
{
intros n.
unfold even.
replace (2*n+2) with (2*(S n)) by lia.
unfold psy; rewrite div2_2p0; trivial.
}
assert (Hpsy_odd : forall n, psy (odd n) = phi n).
{
intros n.
unfold odd, psy; rewrite div2_2p1; trivial; destruct n; auto.
}
exists psy.
unfold dc_list_h10c; constructor; try reflexivity.
apply Forall_app; split; apply Forall_forall.
*
intros c; rewrite in_map_iff.
intros (k & Hk); revert Hk.
unfold dc_list_const; rewrite list_an_spec.
intros (H1 & H2).
unfold h10c_nat in H1.
destruct k as [ | k ]; rewrite <- H1; simpl; auto.
repeat rewrite Hpsy_even.
rewrite Hpsy_0; lia.
*
intros c; rewrite in_map_iff.
intros (k & H1 & H2).
rewrite <- H1, <- dc_h10c_equiv with (φ := phi); auto.
rewrite Forall_forall in Hphi; auto.
+
intros (psy & Hpsy).
simpl in Hpsy.
apply Forall_cons_inv in Hpsy.
destruct Hpsy as (H1 & H2).
apply Forall_app in H2.
destruct H2 as (H2 & H3).
rewrite Forall_forall in H2.
rewrite Forall_forall in H3.
exists (fun n => psy (odd n)).
rewrite Forall_forall.
intros c Hc.
rewrite dc_h10c_equiv with (Ψ := psy); auto.
*
apply H3, in_map_iff; exists c; auto.
*
assert (forall n, n <= dc_max l -> h10c_sem (h10c_nat n) psy) as H4.
{
intros n Hn; apply H2, in_map_iff; exists n; split; auto.
apply list_an_spec; lia.
}
simpl in H1.
clear H2 H3.
intros n Hn.
apply dc_list_const_prop with (1 := Hc) in Hn.
apply list_an_spec in Hn.
clear Hc.
assert (n <= dc_max l) as H5 by lia.
clear Hn.
revert n H4 H5; generalize (dc_max l).
intros m n H2.
induction n as [ | n IHn ]; intros Hn; specialize (H2 _ Hn); simpl in H2.
-
lia.
-
Admitted.

Theorem DIO_ELEM_H10C_SAT : DIO_ELEM_SAT ⪯ H10C_SAT.
Proof.
exists f.
intros (l,ν); simpl; unfold H10C_SAT; rewrite dc_list_h10c_spec.
Admitted.

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
