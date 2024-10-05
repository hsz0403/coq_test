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

Lemma is_safe_environment_Gamma0 : Forall (is_safe_poly_type 0) Gamma0.
Proof.
do 3 (constructor; first by move=> /=; lia).
Admitted.

Lemma is_safe_environment_Ut {ts} : Forall (is_safe_poly_type 0) (map Ut ts).
Proof.
apply /Forall_mapP /Forall_forall => ? _ /=.
Admitted.

Lemma is_safe_environment_St {tSs} : Forall (is_safe_poly_type 0) (map St tSs).
Proof.
apply /Forall_mapP /Forall_forall => [[[? ?] ?]] _ /=.
Admitted.

Lemma is_safe_environment_Pt {tPs} : Forall (is_safe_poly_type 0) (map Pt tPs).
Proof.
apply /Forall_mapP /Forall_forall => [[[? ?] ?]] _ /=.
Admitted.

Lemma iipc2_to_dE {x y: nat} : dt < x -> dt < y -> iipc2 GammaC (poly_arr (to_d (poly_var x)) (to_d (poly_var y))) -> x = y.
Proof.
move=> Hx Hy /iipc2_poly_arrE /iipc2_poly_arrE /iipc2_is_safe_environment.
move=> [:HGamma].
rewrite [GammaC]lock.
apply: unnest.
{
abstract: HGamma.
rewrite -lock.
by do ? (constructor; first by move=> /=; lia).
}
move=> [ss] [ts] /= [].
move=> [| [|]].
-
move=> /last_poly_var_safe_poly_type [].
by lia.
-
have -> : to_d (poly_var x) = safe_poly_type 0 [poly_var x] dt by done.
move=> /safe_poly_type_eqE [+] [<- _].
case: ts; last done.
move=> _ /Forall_inv /iipc2_is_safe_environment => /(_ HGamma).
move=> [ss'] [ts'] /= [].
move=> [| [|]].
+
by move=> /last_poly_var_safe_poly_type [] <-.
+
move=> /safe_poly_type_eqE.
by lia.
+
rewrite -lock /GammaC in_map_iff => [[?]] [+].
move=> /last_poly_var_safe_poly_type [->] /in_seq.
move: Hx.
rewrite /dt.
by lia.
-
rewrite -lock /GammaC.
move=> /in_map_iff [?] [].
move=> /last_poly_var_safe_poly_type [->] /in_seq.
move: Hx.
rewrite /dt.
Admitted.

Lemma to_d_typingI s t Gamma : iipc2 Gamma (poly_arr (poly_arr s t) (poly_arr (to_d t) (to_d s))).
Proof.
eexists.
apply /typing_abs /typing_abs /typing_abs /typing_app.
-
apply: (typing_var (x := 1)).
by reflexivity.
-
apply: typing_app.
+
apply: (typing_var (x := 2)).
by reflexivity.
+
apply: (typing_var (x := 0)).
Admitted.

Lemma encodes_natI (n: nat) : encodes_nat (poly_var (n + zt)) n.
Proof.
Admitted.

Lemma encodes_nat_transport {s t n n'} : iipc2 GammaC (poly_arr (to_d s) (to_d t)) -> encodes_nat s n -> encodes_nat t n' -> n = n'.
Proof.
move=> + [Hn _] [_ Hn'].
move: Hn => /iipc2_poly_arr_comp H /H{H}.
move: Hn' => + /iipc2_poly_arr_comp H => /H{H} /iipc2_to_dE.
rewrite /dt /zt /zt'.
Admitted.

Lemma subst_poly_type_Ut' {ts t} : let σ := fold_right scons poly_var ts in subst_poly_type σ (Ut' (length ts) t) = Ut (subst_poly_type σ t).
Proof.
Admitted.

Lemma subst_poly_type_St' {ts t1 t2 t3} : let σ := fold_right scons poly_var ts in subst_poly_type σ (St' (length ts) (t1, t2, t3)) = St (subst_poly_type σ t1, subst_poly_type σ t2, subst_poly_type σ t3).
Proof.
Admitted.

Lemma last_poly_var_t_cs : last_poly_var t_cs = Some tt.
Proof.
rewrite /t_cs.
move: (_ ++ _) => ss.
move: (tt) => x.
elim: (δ) x.
-
move=> x.
by elim: ss.
-
move=> n + x /=.
have ->: S (n + x) = n + S x by lia.
Admitted.

Lemma generalize_Gamma0 {GammaU GammaS GammaP t} : iipc2 (Gamma0 ++ GammaU ++ GammaS ++ GammaP) t -> iipc2 ([poly_var tt] ++ GammaU ++ GammaS ++ GammaP) t.
Proof.
move: (GammaU ++ GammaS ++ GammaP) => ?.
apply: iipc2_generalization.
do 3 (constructor; first by (apply: last_poly_var_typingI; left)).
constructor; first by (apply: last_poly_var_typingI; rewrite last_poly_var_t_cs; left).
Admitted.

Lemma generalize_GammaU {Gamma GammaS GammaP tUs t} : iipc2 (Gamma ++ map Ut tUs ++ GammaS ++ GammaP) t -> iipc2 (Gamma ++ [poly_var ut] ++ GammaS ++ GammaP) t.
Proof.
move: (GammaS ++ GammaP) => GammaSP.
apply: iipc2_generalization.
apply /Forall_forall => ?.
case /in_app_iff; first by (move=> ?; apply: iipc2_var_InI; rewrite ?in_app_iff; tauto).
case /in_app_iff; last by (move=> ?; apply: iipc2_var_InI; rewrite ?in_app_iff; tauto).
move=> /in_map_iff [?] [<- _].
apply /last_poly_var_typingI /in_app_r.
Admitted.

Lemma generalize_GammaS {Gamma GammaU GammaP tSs t} : iipc2 (Gamma ++ GammaU ++ map St tSs ++ GammaP) t -> iipc2 (Gamma ++ GammaU ++ [poly_var st] ++ GammaP) t.
Proof.
apply: iipc2_generalization.
apply /Forall_forall => ?.
case /in_app_iff; first by (move=> ?; apply: iipc2_var_InI; rewrite ?in_app_iff; tauto).
case /in_app_iff; first by (move=> ?; apply: iipc2_var_InI; rewrite ?in_app_iff; tauto).
case /in_app_iff; last by (move=> ?; apply: iipc2_var_InI; rewrite ?in_app_iff; tauto).
move=> /in_map_iff [[[? ?]?]] [<- _].
apply /last_poly_var_typingI /in_app_r /in_app_r.
Admitted.

Lemma generalize_GammaP {Gamma GammaU GammaS tPs t} : iipc2 (Gamma ++ GammaU ++ GammaS ++ map Pt tPs ) t -> iipc2 (Gamma ++ GammaU ++ GammaS ++ [poly_var pt]) t.
Proof.
apply: iipc2_generalization.
apply /Forall_forall => ?.
do 3 (case /in_app_iff; first by (move=> ?; apply: iipc2_var_InI; rewrite ?in_app_iff; tauto)).
move=> /in_map_iff [[[? ?]?]] [<- _].
apply /last_poly_var_typingI /in_app_r /in_app_r /in_app_r.
Admitted.

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
Admitted.

Lemma iipc2_Ut_unique {xs tSs tPs t} : iipc2 (Gamma0 ++ map Ut (map (fun x : nat => poly_var (x + zt)) xs) ++ map St tSs ++ map Pt tPs) (Ut t) -> exists n, encodes_nat t n.
Proof.
move=> /generalize_Gamma0 /generalize_GammaS /generalize_GammaP.
move=> /iipc2_poly_arrE /iipc2_poly_arrE /iipc2_is_safe_environment.
apply: unnest.
{
do 3 (constructor; first by move=> /=; lia).
apply: Forall_appI; first by apply: is_safe_environment_Ut.
by do 2 (constructor; first by move=> /=; lia).
}
rewrite [[poly_var tt]]lock [[poly_var st]]lock [[poly_var pt]]lock.
move=> [ss'] [ts'] [+ Hss] => /=.
rewrite -lock /= in_app_iff in_map_iff /=.
do 3 (case; first by move=> /last_poly_var_safe_poly_type).
case; first last.
{
unlock.
do 2 (case; first by move=> /last_poly_var_safe_poly_type).
done.
}
move=> [tx].
rewrite in_map_iff.
move=> [Hx] [x] [?] Hxxs.
subst tx.
exists x.
move: Hx Hss => /(congr1 parameters_poly_arr).
rewrite parameters_poly_arr_safe_poly_type /=.
case: ts'; last done.
move=> /= <-.
rewrite ?app_comm_cons.
move=> /Forall_consP [+ /Forall_consP [+ _]].
rewrite ?subst_poly_type_poly_var.
unlock.
move=> /generalize_GammaU H1 /generalize_GammaU H2.
constructor.
-
move: H1 => /iipc2_poly_arrE /iipc2_is_safe_environment.
clear.
apply: unnest.
{
by do ? (constructor; first by move=> /=; lia).
}
move=> [ss] [ts] /= [].
do 2 (case; first by move=> /last_poly_var_safe_poly_type).
case; first last.
{
do 4 (case; first by move=> /last_poly_var_safe_poly_type).
done.
}
move=> /(congr1 parameters_poly_arr).
rewrite parameters_poly_arr_safe_poly_type /=.
case: ts; last done.
move=> /= <-.
move=> /Forall_inv [?] /typing_abs /iipc2I.
rewrite subst_poly_type_poly_var.
apply: iipc2_generalization.
by do 6 (constructor; first by (apply: last_poly_var_typingI; firstorder done)).
-
have ? : x + zt <> b2t by (rewrite /dt /zt /zt' /b2t; lia).
move: H2 => /iipc2_poly_arrE /iipc2_is_safe_environment.
apply: unnest.
{
by do ? (constructor; first by move=> /=; lia).
}
move=> [ss] [ts] /= [].
case; first by (move=> /last_poly_var_safe_poly_type; case).
case; first last.
{
do 5 (case; first by move=> /last_poly_var_safe_poly_type).
done.
}
move=> /(congr1 parameters_poly_arr).
rewrite parameters_poly_arr_safe_poly_type /=.
case: ts; last done.
move=> /= <-.
move=> /Forall_inv [?] /typing_abs /iipc2I.
clear.
rewrite subst_poly_type_poly_var.
move=> /iipc2_generalization => /(_ GammaC).
apply: unnest.
{
by do 6 (constructor; first by (apply: last_poly_var_typingI; firstorder done)).
}
move=> [?] /(typing_app _) H.
Admitted.

Lemma generalize_GammaC {s t t1 t2 t3}: iipc2 (to_d s :: [poly_arr (to_d t3) (poly_var b3t); poly_arr (to_d t2) (poly_var b2t); poly_arr (to_d t1) (poly_var b1t); poly_var tt] ++ [poly_var ut] ++ [poly_var st] ++ [poly_var pt]) (to_d t) -> iipc2 GammaC (poly_arr (to_d s) (to_d t)).
Proof.
move=> [?] /typing_abs /iipc2I /iipc2_generalization.
apply.
Admitted.

Lemma encodes_nat_transport' {x s t1 t2 t3 n n1 n2 n3} : iipc2 ([poly_arr (to_d t3) (poly_var b3t); poly_arr (to_d t2) (poly_var b2t); poly_arr (to_d t1) (poly_var b1t); poly_var tt] ++ [poly_var ut] ++ [poly_var st] ++ [poly_var pt]) (poly_arr (to_d s) (poly_var x)) -> encodes_nat t1 n1 -> encodes_nat t2 n2 -> encodes_nat t3 n3 -> encodes_nat s n -> (x = b1t -> n = n1) /\ (x = b2t -> n = n2) /\ (x = b3t -> n = n3).
Proof.
have : (x <> b1t /\ x <> b2t /\ x <> b3t) \/ (x = b1t) \/ (x = b2t) \/ (x = b3t) by lia.
case; first by lia.
move=> Hx.
move=> /iipc2_poly_arrE /iipc2_is_safe_environment.
apply: unnest.
{
by do ? (constructor; first by move=> /=; lia).
}
move=> [ss] [ts] [+ Hss] => /=.
case; first by move=> /last_poly_var_safe_poly_type [] ?; subst x.
case.
{
move=> /copy [/(congr1 parameters_poly_arr) + /last_poly_var_safe_poly_type [{}Hx]].
rewrite parameters_poly_arr_safe_poly_type /=.
case: ts Hss; last done.
move=> /= + ?.
subst x ss.
move=> /Forall_inv.
rewrite subst_poly_type_poly_var.
by move=> /generalize_GammaC /encodes_nat_transport H _ _ /H {}H /H{H} ->.
}
case.
{
move=> /copy [/(congr1 parameters_poly_arr) + /last_poly_var_safe_poly_type [{}Hx]].
rewrite parameters_poly_arr_safe_poly_type /=.
case: ts Hss; last done.
move=> /= + ?.
subst x ss.
move=> /Forall_inv.
rewrite subst_poly_type_poly_var.
by move=> /generalize_GammaC /encodes_nat_transport H _ /H {}H _ /H{H} ->.
}
case.
{
move=> /copy [/(congr1 parameters_poly_arr) + /last_poly_var_safe_poly_type [{}Hx]].
rewrite parameters_poly_arr_safe_poly_type /=.
case: ts Hss; last done.
move=> /= + ?.
subst x ss.
move=> /Forall_inv.
rewrite subst_poly_type_poly_var.
by move=> /generalize_GammaC /encodes_nat_transport H /H {}H _ _ /H{H} ->.
}
Admitted.

Lemma iipc2_St_soundness {xs tSs tPs t1 t2 t3 n1 n2 n3} : iipc2 (Gamma0 ++ map Ut (map (fun x : nat => poly_var (x + zt)) xs) ++ map St tSs ++ map Pt tPs) (St (t1, t2, t3)) -> Forall encodes_sum tSs -> encodes_nat t1 n1 -> encodes_nat t2 n2 -> encodes_nat t3 n3 -> n1 + n2 = n3.
Proof.
move=> /generalize_Gamma0 /generalize_GammaU /generalize_GammaP.
move=> + HtSs /= => /iipc2_poly_arrE /iipc2_poly_arrE /iipc2_poly_arrE /iipc2_is_safe_environment.
apply: unnest.
{
do 5 (constructor; first by move=> /=; lia).
apply: Forall_appI; first by apply: is_safe_environment_St.
by (constructor; first by move=> /=; lia).
}
move=> [ss'] [ts'] [+ Hss] => /=.
do 5 (case; first by move=> /last_poly_var_safe_poly_type).
move /in_app_iff.
case; last by case; [move=> /last_poly_var_safe_poly_type | done].
move=> /in_map_iff [[[s1 s2] s3]] /= [/(congr1 parameters_poly_arr)].
rewrite parameters_poly_arr_safe_poly_type /=.
move=> Hss'.
case: ts' Hss' Hss; last done.
rewrite /length => <-.
rewrite map_subst_poly_type_poly_var ?app_comm_cons.
move=> /Forall_consP [/generalize_GammaS H1] /Forall_consP [/generalize_GammaS H2] /Forall_consP [/generalize_GammaS H3] _.
move: HtSs => /Forall_forall => H /H{H} /= [n1'] [n2'] [n3'] [Hn1'] [Hn2'] [Hn3'] + Hn1 Hn2 Hn3.
have := encodes_nat_transport' H1 Hn1 Hn2 Hn3 Hn1'.
have := encodes_nat_transport' H2 Hn1 Hn2 Hn3 Hn2'.
have := encodes_nat_transport' H3 Hn1 Hn2 Hn3 Hn3'.
clear.
rewrite /b1t /b2t /b3t.
Admitted.

Lemma subst_poly_type_Pt' {ts t1 t2 t3} : let σ := fold_right scons poly_var ts in subst_poly_type σ (Pt' (length ts) (t1, t2, t3)) = Pt (subst_poly_type σ t1, subst_poly_type σ t2, subst_poly_type σ t3).
Proof.
by rewrite /= ?fold_right_length_ts.
