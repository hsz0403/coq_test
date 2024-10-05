Require Import List Lia.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts term_facts typing_facts iipc2_facts sn_facts.
Require Import Undecidability.DiophantineConstraints.H10C.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Local Arguments nth_error_In {A l n x}.
Local Arguments In_nth_error {A l x}.
Local Arguments Forall_inv {A P a l}.
Local Arguments Forall_inv_tail {A P a l}.
Module SafePolyType.
Local Fixpoint is_safe_poly_arr (n: nat) (t: poly_type) := match t with | poly_var x => n <= x | poly_arr _ t => is_safe_poly_arr n t | poly_abs _ => False end.
Fixpoint is_safe_poly_type (n: nat) (t: poly_type) := if t is poly_abs t then is_safe_poly_type (1+n) t else is_safe_poly_arr n t.
Definition safe_poly_type (n: nat) (ts: list poly_type) (x: nat) := many_poly_abs n (many_poly_arr ts (poly_var (n + x))).
End SafePolyType.
Module Argument.
Import SafePolyType.
Section H10C_SAT_to_SysF_INH.
Variable h10cs : list h10c.
Fixpoint variable_bound (h10cs : list h10c) : nat := match h10cs with | [] => 0 | (h10c_one x) :: h10cs => 1 + x + variable_bound h10cs | (h10c_plus x y z) :: h10cs => 1 + x + y + z + variable_bound h10cs | (h10c_mult x y z) :: h10cs => 1 + x + y + z + variable_bound h10cs end.
Definition δ := variable_bound h10cs.
Definition tt := 0.
Definition ut := 1.
Definition st := 2.
Definition pt := 3.
Definition b1t := 4.
Definition b2t := 5.
Definition b3t := 6.
Definition GammaC := map poly_var (seq 0 7).
Arguments GammaC : simpl never.
Definition dt := 7.
Definition to_d' d (t: poly_type) := poly_arr t (poly_var (d+dt)).
Definition to_d := to_d' 0.
Definition Ut' d t := many_poly_arr [poly_arr (to_d' d t) (poly_var (d+b1t)); poly_arr t (poly_var (d+b2t))] (poly_var (d+ut)).
Definition Ut := Ut' 0.
Definition St' d := fun '(t1, t2, t3) => many_poly_arr [poly_arr (to_d' d t1) (poly_var (d+b1t)); poly_arr (to_d' d t2) (poly_var (d+b2t)); poly_arr (to_d' d t3) (poly_var (d+b3t))] (poly_var (d+st)).
Definition St := St' 0.
Definition Pt' d := fun '(t1, t2, t3) => many_poly_arr [poly_arr (to_d' d t1) (poly_var (d+b1t)); poly_arr (to_d' d t2) (poly_var (d+b2t)); poly_arr (to_d' d t3) (poly_var (d+b3t))] (poly_var (d+pt)).
Definition Pt := Pt' 0.
Definition zt' d := d + 10.
Definition zt := zt' 0.
Definition t_u := poly_abs (many_poly_arr [ Ut' 1 (poly_var 0); (* forall x *) Ut' 1 (poly_var 0); Ut' 1 (poly_var 0); Ut' 1 (poly_var 0); poly_abs (many_poly_arr [ (* exists y *) Ut' 2 (poly_var 0); (* y is in universe *) St' 2 ((poly_var 1), (poly_var (1+ zt' 2)), (poly_var 0)); (* x + 1 = y *) St' 2 ((poly_var 0), (poly_var (0+ zt' 2)), (poly_var 0)); (* y + 0 = 0 *) Pt' 2 ((poly_var 0), (poly_var (0+ zt' 2)), (poly_var (0+ zt' 2))) (* y * 0 = 0*) ] (poly_var (2+tt))) ] (poly_var (1+tt))).
Definition t_s := many_poly_abs 5 (many_poly_arr [ poly_arr (St' 5 ((poly_var 0), (poly_var 3), (poly_var 4))) (poly_var (5+tt)); (* have a + d = e *) Ut' 5 (poly_var 0); Ut' 5 (poly_var 1); Ut' 5 (poly_var 2); Ut' 5 (poly_var 3); Ut' 5 (poly_var 4); (* for a b c d e such that *) St' 5 ((poly_var 0), (poly_var 1), (poly_var 2)); (* a + b = c *) St' 5 ((poly_var 1), (poly_var (1 + zt' 5)), (poly_var 3)); (* b + 1 = d *) St' 5 ((poly_var 2), (poly_var (1 + zt' 5)), (poly_var 4)) (* c + 1 = e *) ] (poly_var (5+tt))).
Definition t_p := many_poly_abs 5 (many_poly_arr [ poly_arr (Pt' 5 ((poly_var 0), (poly_var 3), (poly_var 4))) (poly_var (5+tt)); (* have a * d = e *) Ut' 5 (poly_var 0); Ut' 5 (poly_var 1); Ut' 5 (poly_var 2); Ut' 5 (poly_var 3); Ut' 5 (poly_var 4); (* for a b c d e such that *) Pt' 5 ((poly_var 0), (poly_var 1), (poly_var 2)); (* a * b = c *) St' 5 ((poly_var 1), (poly_var (1 + zt' 5)), (poly_var 3)); (* b + 1 = d *) St' 5 ((poly_var 2), (poly_var 0), (poly_var 4)) (* c + a = e *) ] (poly_var (5+tt))).
Definition h10c_poly_type (c: h10c) : poly_type := match c with | (h10c_one x) => St' δ (poly_var x, poly_var (δ + zt), poly_var (δ+1+zt)) | (h10c_plus x y z) => St' δ (poly_var x, poly_var y, poly_var z) | (h10c_mult x y z) => Pt' δ (poly_var x, poly_var y, poly_var z) end.
Definition t_cs := many_poly_abs δ (many_poly_arr (map (fun x => Ut' δ (poly_var x)) (seq 0 δ) ++ map h10c_poly_type h10cs) (poly_var (δ + tt))).
Definition Gamma0 := [t_u; t_s; t_p; t_cs].
Definition GammaH := Gamma0 ++ (map Ut (map (fun x => poly_var (x + zt)) [0; 1])) ++ (map St [ (poly_var zt, poly_var zt, poly_var zt); (poly_var (1+zt), poly_var zt, poly_var (1+zt)); (poly_var zt, poly_var (1+zt), poly_var (1+zt))]) ++ (map Pt [(poly_var zt, poly_var zt, poly_var zt); (poly_var (1+zt), poly_var zt, poly_var zt)]).
Arguments Gamma0 : simpl never.
Arguments Ut' : simpl never.
Arguments St' : simpl never.
Arguments St : simpl never.
Arguments Pt' : simpl never.
Arguments Pt : simpl never.
Definition encodes_nat (t: poly_type) (n: nat) := iipc2 GammaC (poly_arr (to_d (poly_var (n + zt))) (to_d t)) /\ iipc2 GammaC (poly_arr (to_d t) (to_d (poly_var (n + zt)))).
Definition encodes_sum := fun '(t1, t2, t3) => exists n1 n2 n3, encodes_nat t1 n1 /\ encodes_nat t2 n2 /\ encodes_nat t3 n3 /\ n1 + n2 = n3.
Definition encodes_prod := fun '(t1, t2, t3) => exists n1 n2 n3, encodes_nat t1 n1 /\ encodes_nat t2 n2 /\ encodes_nat t3 n3 /\ n1 * n2 = n3.
Section InverseTransport.
End InverseTransport.
Section Transport.
Variable φ : nat -> nat.
Variable Hφ : forall c, In c h10cs -> h10c_sem c φ.
Fixpoint value_bound (cs: list h10c) : nat := match cs with | [] => 0 | (h10c_one x) :: cs => 1 + φ x + value_bound cs | (h10c_plus x y z) :: cs => 1 + φ x + φ y + φ z + value_bound cs | (h10c_mult x y z) :: cs => 1 + φ x + φ y + φ z + value_bound cs end.
Definition poly_num n := poly_var (n+zt).
Definition GammaU n := map (fun i => Ut (poly_num i)) (seq 0 (1+n)).
Definition GammaS0 n := map (fun i => St (poly_num i, poly_num 0, poly_num i)) (seq 0 (1+n)).
Definition GammaS1 n := map (fun i => St (poly_num i, poly_num 1, poly_num (1+i))) (seq 0 n).
Definition GammaP0 n := map (fun i => Pt (poly_num i, poly_num 0, poly_num 0)) (seq 0 (1+n)).
Definition GammaUSP n := locked (GammaU (S n) ++ (GammaS0 (S n) ++ GammaS1 (S n)) ++ GammaP0 (S n)).
Definition h10cφ_poly_type (c: h10c) : poly_type := match c with | (h10c_one x) => St (poly_num (φ x), poly_num 0, poly_num 1) | (h10c_plus x y z) => St (poly_num (φ x), poly_num (φ y), poly_num (φ z)) | (h10c_mult x y z) => Pt (poly_num (φ x), poly_num (φ y), poly_num (φ z)) end.
Definition Gammaφ := map h10cφ_poly_type h10cs.
Fact GammaUSn {n} : GammaU (S n) = GammaU n ++ [Ut (poly_num (1+n))].
Proof.
by rewrite /GammaU (ltac:(lia) : 1 + S n = (S n) + 1) [seq _ (S n + 1)]seq_app map_app.
Fact GammaS0Sn {n} : GammaS0 (S n) = GammaS0 n ++ [St (poly_num (1+n), poly_num 0, poly_num (1+n))].
Proof.
by rewrite /GammaS0 (ltac:(lia) : 1 + S n = (S n) + 1) [seq _ (S n + 1)]seq_app map_app.
Fact GammaS1Sn {n} : GammaS1 (S n) = GammaS1 n ++ [St (poly_num n, poly_num 1, poly_num (1+n))].
Proof.
by rewrite (ltac:(lia) : S n = n + 1) /GammaS1 seq_app map_app.
Fact GammaP0Sn {n} : GammaP0 (S n) = GammaP0 n ++ [Pt (poly_num (1+n), poly_num 0, poly_num 0)].
Proof.
by rewrite /GammaP0 (ltac:(lia) : 1 + S n = (S n) + 1) [seq _ (S n + 1)]seq_app map_app.
Local Arguments GammaU : simpl never.
Local Arguments GammaS0 : simpl never.
Local Arguments GammaS1 : simpl never.
Local Arguments GammaP0 : simpl never.
Definition ϵ := fold_right (Nat.add) 0 (map φ (seq 0 δ)).
End Transport.
End H10C_SAT_to_SysF_INH.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma subst_poly_type_h10c_poly_type {ts c} : let σ := (fold_right scons poly_var (rev ts)) in δ = length ts -> subst_poly_type σ (h10c_poly_type c) = match c with | (h10c_one x) => St (σ x, poly_var zt, poly_var (1+zt)) | (h10c_plus x y z) => St (σ x, σ y, σ z) | (h10c_mult x y z) => Pt (σ x, σ y, σ z) end.
Proof.
move=> σ Hts.
subst σ.
case: c.
-
move=> x.
rewrite /= Hts -rev_length ?fold_right_length_ts.
have -> : length (rev ts) + 1 + zt = length (rev ts) + (1 + zt) by lia.
by rewrite fold_right_length_ts.
-
move=> >.
by rewrite /= Hts -rev_length ?fold_right_length_ts.
-
move=> >.
by rewrite /= Hts -rev_length ?fold_right_length_ts.
