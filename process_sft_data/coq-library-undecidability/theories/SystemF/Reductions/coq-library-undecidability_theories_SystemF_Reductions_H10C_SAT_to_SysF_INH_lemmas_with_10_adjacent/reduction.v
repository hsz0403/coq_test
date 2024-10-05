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

Fact GammaP0Sn {n} : GammaP0 (S n) = GammaP0 n ++ [Pt (poly_num (1+n), poly_num 0, poly_num 0)].
Proof.
Admitted.

Lemma in_Ut_GammaUSP {i n} : i <= 1 + n -> In (Ut (poly_num i)) (GammaUSP n).
Proof.
move=> ?.
rewrite /GammaUSP -lock /GammaU.
apply /in_app_l /in_map_iff.
exists i.
Admitted.

Lemma in_St1_GammaUSP {i n} : i <= n -> In (St (poly_num i, poly_num 1, poly_num (1+i))) (GammaUSP n).
Proof.
move=> ?.
rewrite /GammaUSP -lock /GammaS1.
apply /in_app_r /in_app_l /in_app_r.
apply /in_map_iff.
exists i.
Admitted.

Lemma introduce_Uts (n: nat) : iipc2 (Gamma0 ++ GammaUSP n) (poly_var tt) -> iipc2 GammaH (poly_var tt).
Proof.
elim: n; first by rewrite /GammaUSP; unlock.
move=> n + HSn.
apply.
apply: (iipc2_poly_varI 0 (ts := [poly_num (1+n)])); first by reflexivity.
rewrite [Gamma0]lock /map subst_poly_type_Ut' [many_poly_arr]lock /=.
move=> [:HUt0].
constructor.
{
abstract: HUt0.
by apply /iipc2_var_InI /in_app_r /in_Ut_GammaUSP.
}
do 3 (constructor; first done).
clear HUt0.
constructor; last done.
apply: (iipc2_poly_absI (S (S n) + zt)).
-
clear.
have ->: S (S n) + zt = S (S zt) + n by lia.
apply /Forall_appI.
{
rewrite -lock.
do 3 (constructor; first by apply /fresh_inP).
constructor; last done.
rewrite /t_cs /tt.
apply /fresh_in_many_poly_absI /fresh_in_many_poly_arrI; last by lia.
apply /Forall_appI.
+
apply /Forall_mapP /Forall_seqP => x ?.
rewrite /fresh_in /= /dt /b1t /b2t /ut.
by lia.
+
have := δP.
move=> H.
apply /Forall_mapP.
apply: Forall_impl H.
case=> > /=; rewrite /fresh_in /= /dt /b1t /b2t /b3t /ut /st /pt /zt /zt'; by lia.
}
rewrite /GammaUSP -lock.
apply /Forall_appI; [| apply /Forall_appI; [apply /Forall_appI |]]; apply /Forall_mapP /Forall_seqP; firstorder (by [|move=> /=; lia]).
-
set σ := (σ in subst_poly_type σ _).
have Hσ: forall x, σ x = (scons (poly_var 0) (scons (poly_var (S (S n) + zt)) (funcomp poly_var S))) x by move=> [|[|x]].
under ext_poly_type => ? do rewrite Hσ.
have ->: S (S n) + zt = S (S zt) + n by lia.
unlock.
by firstorder by [|lia].
-
rewrite poly_type_norm.
set σ := (σ in subst_poly_type σ _).
have Hσ: forall x, σ x = fold_right scons poly_var [poly_var (S (S n) + zt); poly_var (S n + zt)] x by move=> [|[|x]].
under ext_poly_type => ? do rewrite Hσ.
clear σ Hσ.
set σ := (σ in subst_poly_type σ _).
rewrite -[locked many_poly_arr]lock [Ut']lock [St']lock [Pt']lock /= -[locked Ut']lock -[locked St']lock -[locked Pt']lock ?subst_poly_type_Ut' ?subst_poly_type_St' ?subst_poly_type_Pt' /=.
do 4 (apply: iipc2_poly_arrI).
apply: iipc2_weakening HSn.
clear.
move=> t.
rewrite /GammaUSP -?lock [Gamma0]lock GammaUSn GammaS0Sn GammaS1Sn GammaP0Sn.
rewrite [GammaU]lock [GammaS0]lock [GammaS1]lock [GammaP0]lock /= ?in_app_iff /=.
Admitted.

Lemma introduce_Sts (n n1 n2: nat) (Gamma: environment): n1 + n2 <= S n -> iipc2 (locked Gamma0 ++ GammaUSP n ++ (St (poly_num n1, poly_num n2, poly_num (n1+n2)) :: Gamma)) (poly_var tt) -> iipc2 (locked Gamma0 ++ GammaUSP n ++ Gamma) (poly_var tt).
Proof.
elim: n2 => [| n2 IH] ?.
-
apply: iipc2_weakening => t.
rewrite ?in_app_iff /=.
case; first by tauto.
case; first by tauto.
case; last by tauto.
move=> <-.
right.
left.
rewrite /GammaUSP -lock.
apply /in_app_r /in_app_l /in_app_l.
apply /in_map_iff.
exists n1.
have ->: n1 + 0 = n1 by lia.
constructor; first done.
apply /in_seq.
by lia.
-
move=> H.
apply: IH; first by lia.
rewrite -[_ Gamma0]lock.
apply: (iipc2_poly_varI 1 (ts := [poly_num (n1 + (S n2)); poly_num (S n2); poly_num (n1 + n2); poly_num n2; poly_num n1])); first by reflexivity.
rewrite [Gamma0]lock /map ?subst_poly_type_Ut' ?subst_poly_type_St' /(subst_poly_type _ (poly_arr _ _)) -/subst_poly_type subst_poly_type_St' /subst_poly_type /=.
have HUSP t Gamma' : In t (GammaUSP n) -> iipc2 (locked Gamma0 ++ GammaUSP n ++ Gamma') t.
{
move=> ?.
apply: iipc2_var_InI.
by apply /in_app_r /in_app_l.
}
constructor.
{
apply: iipc2_poly_arrI.
apply: iipc2_weakening H => ?.
rewrite /= ?app_comm_cons ?in_app_iff /=.
clear.
by tauto.
}
do 5 (constructor; first by (apply: HUSP; apply: in_Ut_GammaUSP; by lia)).
constructor.
{
apply: iipc2_var_InI.
rewrite ?in_app_iff /=.
by tauto.
}
constructor; first by (apply: HUSP; apply: in_St1_GammaUSP; by lia).
constructor; last done.
have ->: n1 + S n2 = S (n1 + n2) by lia.
apply /HUSP /in_St1_GammaUSP.
Admitted.

Lemma introduce_Pts (n n1 n2: nat) (Gamma: environment): n1 <= S n -> n2 <= S n -> n1 * n2 <= S n -> iipc2 (locked Gamma0 ++ GammaUSP n ++ (Pt (poly_num n1, poly_num n2, poly_num (n1*n2)) :: Gamma)) (poly_var tt) -> iipc2 (locked Gamma0 ++ GammaUSP n ++ Gamma) (poly_var tt).
Proof.
elim: n2 Gamma => [| n2 IH] Gamma ? ? ?.
-
apply: iipc2_weakening => t.
rewrite ?in_app_iff /=.
case; first by tauto.
case; first by tauto.
case; last by tauto.
move=> <-.
right.
left.
rewrite /GammaUSP -lock.
apply /in_app_r /in_app_r.
apply /in_map_iff.
exists n1.
have ->: n1 * 0 = 0 by lia.
constructor; first done.
apply /in_seq.
by lia.
-
move=> H.
apply: (introduce_Sts n (n1 * n2) n1); first by lia.
apply: IH; [by lia | by lia | by lia |].
rewrite -[_ Gamma0]lock.
apply: (iipc2_poly_varI 2 (ts := [poly_num (n1 * (S n2)); poly_num (S n2); poly_num (n1 * n2); poly_num n2; poly_num n1])); first by reflexivity.
rewrite [Gamma0]lock /map ?subst_poly_type_Ut' ?subst_poly_type_St' subst_poly_type_Pt' /(subst_poly_type _ (poly_arr _ _)) -/subst_poly_type subst_poly_type_Pt' /subst_poly_type /=.
have HUSP t Gamma' : In t (GammaUSP n) -> iipc2 (locked Gamma0 ++ GammaUSP n ++ Gamma') t.
{
move=> ?.
apply: iipc2_var_InI.
by apply /in_app_r /in_app_l.
}
constructor.
{
apply: iipc2_poly_arrI.
apply: iipc2_weakening H => ?.
rewrite /= ?app_comm_cons ?in_app_iff /=.
clear.
by tauto.
}
do 5 (constructor; first by (apply: HUSP; apply: in_Ut_GammaUSP; by lia)).
constructor.
{
apply: iipc2_var_InI.
rewrite ?in_app_iff /=.
by tauto.
}
constructor; first by (apply: HUSP; apply: in_St1_GammaUSP; by lia).
constructor; last done.
have ->: n1 * n2 + n1 = n1 * S n2 by lia.
apply: iipc2_var_InI.
rewrite ?in_app_iff /=.
Admitted.

Lemma ϵP (x: nat) : x < δ -> φ x <= ϵ.
Proof.
suff: Forall (fun x => φ x <= ϵ) (seq 0 δ).
{
move=> + ? => /Forall_forall.
apply.
apply /in_seq.
by lia.
}
rewrite /ϵ.
elim: (seq 0 δ); first by constructor.
move=> {}x xs IH.
constructor.
-
move=> /=.
by lia.
-
apply: Forall_impl IH => ? /=.
Admitted.

Lemma introduce_φ (n: nat): ϵ <= S n -> iipc2 (Gamma0 ++ GammaUSP n ++ Gammaφ) (poly_var tt) -> iipc2 (Gamma0 ++ GammaUSP n) (poly_var tt).
Proof using Hφ.
move: (Hφ).
have := δP.
rewrite /Gammaφ [Gamma0]lock => + /Forall_forall + Hn.
elim: (h10cs); first by rewrite app_nil_r.
move=> [x | x y z | x y z] cs IH /Forall_consP [Hδ /IH {}IH] /Forall_consP /= [Hφc /IH {}IH].
-
rewrite Hφc.
by move=> /introduce_Sts => /(_ ltac:(lia)) /IH.
-
rewrite -Hφc.
move=> /introduce_Sts H.
apply /IH /H.
have := ϵP z.
by lia.
-
rewrite -Hφc.
move=> /introduce_Pts H.
Admitted.

Lemma eliminate_φ: iipc2 (Gamma0 ++ GammaUSP (S ϵ) ++ Gammaφ) (poly_var tt).
Proof.
apply: (iipc2_poly_varI 3 (ts := rev (map (fun x => poly_num (φ x)) (seq 0 δ)))); first by rewrite rev_length map_length seq_length.
rewrite map_app rev_involutive.
apply /Forall_appI.
-
apply /Forall_mapP /Forall_mapP /Forall_seqP => x Hx.
set ts := (map _ _).
have ->: δ = length ts by rewrite /ts map_length seq_length.
rewrite subst_poly_type_Ut' /subst_poly_type /ts fold_right_map_seq; first by lia.
apply /iipc2_var_InI /in_app_r /in_app_l /in_Ut_GammaUSP.
have := ϵP x.
by lia.
-
apply /Forall_mapP /Forall_mapP.
rewrite /Gammaφ.
clear.
have := δP.
elim: (h10cs); first done.
move=> c cs IH.
move=> /Forall_consP [Hc /IH {}IH].
constructor.
+
set ts := (map _ (seq _ _)).
have Hδ: δ = length ts by rewrite /ts map_length seq_length.
move: c Hc {IH} => []; rewrite /h10c_poly_type.
*
move=> x ?.
have ->: δ + 1 + zt = δ + (1 + zt) by lia.
rewrite Hδ subst_poly_type_St' /subst_poly_type ?fold_right_length_ts fold_right_map_seq; first by lia.
apply /iipc2_var_InI /in_app_r /in_app_r.
by left.
*
move=> x y z ?.
rewrite Hδ subst_poly_type_St' /subst_poly_type.
do 3 (rewrite fold_right_map_seq; first by lia).
apply /iipc2_var_InI /in_app_r /in_app_r.
by left.
*
move=> x y z ?.
rewrite Hδ subst_poly_type_Pt' /subst_poly_type.
do 3 (rewrite fold_right_map_seq; first by lia).
apply /iipc2_var_InI /in_app_r /in_app_r.
by left.
+
apply: Forall_impl IH => ?.
apply: iipc2_weakening => ?.
move: (Gamma0) (GammaUSP _) => ? ?.
clear.
rewrite ?in_app_iff /=.
Admitted.

Lemma transport : H10C_SAT h10cs -> SysF_INH (GammaH, poly_var tt).
Proof.
move=> [φ Hφ].
suff: iipc2 GammaH (poly_var tt).
{
move=> [?] /typing_to_type_assignment ?.
eexists; by eassumption.
}
apply: (introduce_Uts (S (ϵ φ))).
apply: (introduce_φ φ Hφ); first by lia.
Admitted.

Theorem reduction : H10C_SAT ⪯ SysF_INH.
Proof.
exists (fun h10cs => (Argument.GammaH h10cs, poly_var Argument.tt)).
move=> h10cs.
constructor.
-
exact: Argument.transport.
-
exact: Argument.inverse_transport.
