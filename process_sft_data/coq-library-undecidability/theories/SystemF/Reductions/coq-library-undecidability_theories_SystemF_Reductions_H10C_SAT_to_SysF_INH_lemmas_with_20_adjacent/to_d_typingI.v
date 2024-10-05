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

Lemma safe_poly_type_eqE {n n' ts ts' x x'} : safe_poly_type n ts x = safe_poly_type n' ts' x' -> n = n' /\ ts = ts' /\ x = x'.
Proof.
elim: n n' x x'.
-
move=> [|?]; last by case: ts.
move=> x x'.
elim: ts ts'.
+
case; last done.
by move=> [].
+
move=> ? ? IH.
case; first done.
by move=> ? ? [] <- /IH [_] [<-] <-.
-
move=> n IH [|n']; first by case: (ts').
move=> x x' [].
have -> : S (n + x) = n + (S x) by lia.
have -> : S (n' + x') = n' + (S x') by lia.
Admitted.

Lemma is_safe_poly_arrE {i t} : is_safe_poly_arr i t -> exists (ts : list poly_type) (x : nat), t = (many_poly_arr ts (poly_var (i+x))).
Proof.
elim: t.
-
move=> /= x *.
exists [], (x-i).
congr poly_var.
by lia.
-
move=> s _ ? IH /= /IH [ts] [x] ->.
by exists (s :: ts), x.
-
Admitted.

Lemma is_safe_poly_typeE {i t} : is_safe_poly_type i t -> exists (n : nat) (ts : list poly_type) (x : nat), t = many_poly_abs n (many_poly_arr ts (poly_var (n + (i + x)))).
Proof.
elim: t i.
-
move=> /= x i *.
exists 0, [], (x-i).
congr poly_var.
by lia.
-
move=> s _ t _ ? /= /is_safe_poly_arrE [ts] [x] ->.
by exists 0, (s :: ts), x.
-
move=> ? IH i /IH [n] [ts] [x] ->.
exists (1+n), ts, x.
move=> /=.
do 4 f_equal.
Admitted.

Lemma typing_safe_poly_typeE {Gamma P n ss x As y} : typing Gamma P (many_poly_abs n (many_poly_arr ss (poly_var (n+x)))) -> typing Gamma (many_argument_app P As) (poly_var y) -> exists (ts : list poly_type) (Qs : list term), x = y /\ As = (map argument_poly_type ts) ++ (map argument_term Qs) /\ n = length ts /\ length ss = length Qs.
Proof.
elim: n P ss x As.
-
move=> P ss x As /=.
elim: ss P As.
+
move=> P [| [?|?] ?].
*
move=> /typing_functional H /H [] ->.
by exists [], [].
*
move=> /= + /typing_many_argument_subterm [?] /typingE [?].
by move=> /typing_functional H [/H].
*
move=> /= + /typing_many_argument_subterm [?] /typingE [?].
by move=> /typing_functional H [_ /H].
+
move=> s ss IH P [| [Q|?] ?] /=.
*
by move=> /typing_functional H /H.
*
move=> + /copy [/IH {}IH].
move=> + /typing_many_argument_subterm [?] /copy [/typingE [?]].
move=> /typing_functional H [/H{H} [<-]] <- ? /IH.
move=> [[| ? ?]] [Qs] [<-] [->] [?] ->; last done.
by exists [], (Q :: Qs).
*
move=> + /typing_many_argument_subterm [?] /typingE [?].
by move=> /typing_functional H [_ /H].
-
move=> n IH P ss x [|A As] /=.
+
by move=> /typing_functional H /H.
+
move: A => [? | s].
*
move=> + /typing_many_argument_subterm [?] /typingE [?].
by move=> /typing_functional H [/H].
*
move=> /typing_ty_app => /(_ s).
rewrite subst_poly_type_many_poly_abs subst_poly_type_many_poly_arr /=.
have ->: S (n + x) = n + S x by lia.
rewrite iter_up_poly_type_poly_type.
move=> /IH {}IH /IH.
move=> [ts] [Qs] [<-] [->] [->].
rewrite map_length.
move=> ->.
Admitted.

Lemma typing_is_safe_environment {Gamma P x} : normal_form P -> typing Gamma P (poly_var x) -> Forall (is_safe_poly_type 0) Gamma -> exists ss y ts Qs, P = many_app (many_ty_app (var y) ts) Qs /\ nth_error Gamma y = Some (safe_poly_type (length ts) ss x) /\ Forall2 (typing Gamma) Qs (map (subst_poly_type (fold_right scons poly_var (rev ts))) ss).
Proof.
case; [ | by move=> > _ /typingE [?] [] | by move=> > _ /typingE [?] []].
move=> {}P /many_argument_appI [y] [As] [-> _].
move=> /copy [/typing_many_argument_subterm [?]].
move=> /copy [/typingE].
move=> + + + /Forall_forall H => /nth_error_In /H{H} /is_safe_poly_typeE.
move=> [n] [ss] [z] -> Hy HyAs.
exists ss, y.
move: (Hy) (HyAs) => /typing_safe_poly_typeE H /H{H}.
move=> [ts] [Qs] [?] [?] [? ?].
exists ts, Qs.
subst x As.
subst n.
constructor; [|constructor].
-
by rewrite many_argument_app_app many_argument_app_map_argument_poly_type many_argument_app_map_argument_term.
-
by move: Hy => /typingE.
-
move: Hy => /typing_many_ty_appI => /(_ ts ltac:(lia)).
move: HyAs.
rewrite many_argument_app_app many_argument_app_map_argument_poly_type.
move: (many_ty_app (var y) _) => {}P.
rewrite subst_poly_type_many_poly_arr many_argument_app_map_argument_term.
move=> /typing_many_app_arguments H /H.
apply.
Admitted.

Corollary iipc2_is_safe_environment {Gamma x} : iipc2 Gamma (poly_var x) -> Forall (is_safe_poly_type 0) Gamma -> exists ss ts, In (safe_poly_type (length ts) ss x) Gamma /\ Forall (iipc2 Gamma) (map (subst_poly_type (fold_right scons poly_var (rev ts))) ss).
Proof.
move=> [P] /typing_normal_form [{}P] [/typing_is_safe_environment H] /H {}H /H.
move=> [ss] [?] [ts] [?] [_] [/nth_error_In ?] /Forall2_typing_Forall_iipc2 ?.
Admitted.

Lemma last_poly_var_safe_poly_type {t n ss x} : t = safe_poly_type n ss x -> last_poly_var t = Some x.
Proof.
move=> ->.
elim: n ss x.
-
move=> + x.
by elim.
-
move=> n /= + ss x.
have ->: S (n + x) = n + S x by lia.
Admitted.

Lemma parameters_poly_arr_safe_poly_type {n ss x}: parameters_poly_arr (safe_poly_type n ss x) = if n is 0 then ss else [].
Proof.
case: n; last done.
elim: ss; first done.
Admitted.

Lemma safe_poly_typeP {n ss x} : is_safe_poly_type 0 (safe_poly_type n ss x).
Proof.
have ->: x = 0 + x by lia.
move: (0) => k.
elim: n k.
-
move=> k.
elim: ss; [move=> /=; by lia | by move=> /= ? [|? ?]].
-
move=> n IH k /=.
have ->: S (n + (k + x)) = n + ((S k) + x) by lia.
Admitted.

Lemma δP : Forall (fun c => match c with | (h10c_one x) => x < δ | (h10c_plus x y z) => x < δ /\ y < δ /\ z < δ | (h10c_mult x y z) => x < δ /\ y < δ /\ z < δ end) h10cs.
Proof.
rewrite /δ.
elim: (h10cs); first by constructor.
move=> c cs IH.
constructor.
-
case: c => /= *; by lia.
-
apply: Forall_impl IH.
Admitted.

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

Lemma subst_poly_type_Pt' {ts t1 t2 t3} : let σ := fold_right scons poly_var ts in subst_poly_type σ (Pt' (length ts) (t1, t2, t3)) = Pt (subst_poly_type σ t1, subst_poly_type σ t2, subst_poly_type σ t3).
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

Lemma iipc2_Pt_soundness {xs tSs tPs t1 t2 t3 n1 n2 n3} : iipc2 (Gamma0 ++ map Ut (map (fun x : nat => poly_var (x + zt)) xs) ++ map St tSs ++ map Pt tPs) (Pt (t1, t2, t3)) -> Forall encodes_prod tPs -> encodes_nat t1 n1 -> encodes_nat t2 n2 -> encodes_nat t3 n3 -> n1 * n2 = n3.
Proof.
move=> /generalize_Gamma0 /generalize_GammaU /generalize_GammaS.
move=> + HtSs /= => /iipc2_poly_arrE /iipc2_poly_arrE /iipc2_poly_arrE /iipc2_is_safe_environment.
apply: unnest.
{
do 6 (constructor; first by move=> /=; lia).
by apply: is_safe_environment_Pt.
}
move=> [ss'] [ts'] [+ Hss] => /=.
rewrite in_map_iff.
do 6 (case; first by move=> /last_poly_var_safe_poly_type).
move=> [[[s1 s2] s3]] /= [/(congr1 parameters_poly_arr)].
rewrite parameters_poly_arr_safe_poly_type /=.
move=> Hss'.
case: ts' Hss' Hss; last done.
rewrite /length => <-.
under [map (subst_poly_type _) _]map_ext => ? do (rewrite subst_poly_type_poly_var).
rewrite map_id ?app_comm_cons.
move=> /Forall_consP [/generalize_GammaP H1] /Forall_consP [/generalize_GammaP H2] /Forall_consP [/generalize_GammaP H3] _.
move: HtSs => /Forall_forall => H /H{H} /= [n1'] [n2'] [n3'] [Hn1'] [Hn2'] [Hn3'] + Hn1 Hn2 Hn3.
have := encodes_nat_transport' H1 Hn1 Hn2 Hn3 Hn1'.
have := encodes_nat_transport' H2 Hn1 Hn2 Hn3 Hn2'.
have := encodes_nat_transport' H3 Hn1 Hn2 Hn3 Hn3'.
clear.
rewrite /b1t /b2t /b3t.
Admitted.

Lemma construct_h10cs_solution {xs tSs tPs P}: normal_form P -> Forall encodes_sum tSs -> Forall encodes_prod tPs -> typing (Gamma0 ++ (map Ut (map (fun x => poly_var (x + zt)) xs)) ++ (map St tSs) ++ (map Pt tPs)) P (poly_var tt) -> H10C_SAT h10cs.
Proof using h10cs.
elim /(measure_ind term_size): P xs tSs tPs => P IH xs tSs tPs + HtSs HtPs.
move=> /copy [HP] /typing_is_safe_environment H /H{H}.
apply: unnest.
{
apply: Forall_appI; first by apply: is_safe_environment_Gamma0.
apply: Forall_appI; first by apply: is_safe_environment_Ut.
apply: Forall_appI; [by apply: is_safe_environment_St | by apply: is_safe_environment_Pt].
}
move=> [ss] [?] [ts] [Qs] [?] [/nth_error_In].
subst P.
case /in_app_iff.
{
case; [|case; [|case; [|case]]]; last done.
-
move: IH HP.
case ts; first by case: ss.
move=> s.
case; last by case ss.
move=> IH HQs [] /(congr1 parameters_poly_arr).
rewrite ?parameters_many_poly_arr.
move=> <- HQsss.
move: (HQsss) => /Forall2_length_eq /=.
move HQs': (Qs) => Qs'.
move: Qs' HQs' => [|]; first done.
move=> Q1 [|]; first done.
move=> Q1' [|]; first done.
move=> Q1'' [|]; first done.
move=> Q1''' [|]; first done.
move=> Q2 [|]; last done.
move=> ? _.
subst Qs.
move: HQs => /normal_form_many_app [_ +].
do 4 (move=> /Forall_inv_tail).
move=> /Forall_inv HQ2.
move: HQsss => /Forall2_consE [/iipc2I HQ1] /Forall2_consE [_] /Forall2_consE [_] /Forall2_consE [_] /Forall2_consE [+ _].
have [n Hsn] : exists n, encodes_nat s n by apply: iipc2_Ut_unique; eassumption.
rewrite [poly_arr _ _]lock [Gamma0]lock /=.
move: HQ2 => /typing_normal_form_poly_absE H /H{H} => /(_ (1+n+zt)) => [[Q2']].
rewrite poly_type_norm.
set f := (f in subst_poly_type f _).
have Hf : forall x, f x = fold_right scons poly_var [poly_var (1 + n + zt); s] x.
{
rewrite /f /funcomp.
case; first done.
case; last done.
by rewrite ?poly_type_norm -[RHS]ren_poly_type_id.
}
under ext_poly_type => ? do rewrite Hf.
set σ := (fold_right _ _ _).
rewrite -?lock [Gamma0]lock [Ut']lock [St']lock [Pt']lock /= -?lock [Gamma0]lock.
rewrite subst_poly_type_Ut' ?subst_poly_type_St' ?subst_poly_type_Pt' /σ /=.
move=> [+] [HQ2'].
move=> /typing_normal_form_poly_arrE H /H{H} [Q2'2] [+] [?].
move=> /typing_normal_form_poly_arrE H /H{H} [Q2'3] [+] [?].
move=> /typing_normal_form_poly_arrE H /H{H} [Q2'4] [+] [?].
move=> /typing_normal_form_poly_arrE H /H{H} [Q2'5] [HQ2'5] [?].
move=> /(typing_weakening (Gamma' := locked Gamma0 ++ (map Ut (map (fun x => poly_var (x + zt)) (1+n :: xs))) ++ (map St ((s, poly_var (1+zt), poly_var (1+n+zt)) :: (poly_var (1+n+zt), poly_var zt, poly_var (1+n+zt)) :: tSs)) ++ (map Pt ((poly_var (1+n+zt), poly_var zt, poly_var zt) :: tPs)))).
apply: unnest.
{
move=> ?.
rewrite /= ?app_comm_cons ?in_app_iff /=.
clear.
by tauto.
}
unlock.
move=> [?] /IH.
apply.
+
rewrite term_size_ren_term /=.
rewrite [_ Q1]term_size_pos [_ Q1']term_size_pos [_ Q1'']term_size_pos [_ Q1''']term_size_pos.
by lia.
+
by apply: normal_form_ren_term.
+
constructor; [| constructor]; last done.
*
exists n, 1, (1+n).
constructor; first done.
do 2 (constructor; first by apply: encodes_natI).
by lia.
*
exists (1+n), 0, (1+n).
do 3 (constructor; first by apply: encodes_natI).
by lia.
+
constructor; last done.
exists (1+n), 0, 0.
do 3 (constructor; first by apply: encodes_natI).
by lia.
-
rewrite /t_s.
rewrite [Gamma0]lock.
move=> /safe_poly_type_eqE [+ [<- _]].
move: ts HP IH.
do 5 (move=> [|?]; first done).
case; last done.
set σ := fold_right scons poly_var _.
move=> /normal_form_many_app [_ HQs] IH _.
rewrite [Ut']lock [St']lock /= -[locked Ut']lock -[locked St']lock ?subst_poly_type_Ut' ?subst_poly_type_St' /= -lock.
move=> /copy [/Forall2_typing_Forall_iipc2 /Forall_consP [_]].
move=> /Forall_consP [/iipc2_Ut_unique [n5 ?]].
move=> /Forall_consP [/iipc2_Ut_unique [n4 ?]].
move=> /Forall_consP [/iipc2_Ut_unique [n3 ?]].
move=> /Forall_consP [/iipc2_Ut_unique [n2 ?]].
move=> /Forall_consP [/iipc2_Ut_unique [n1 ?]].
have ? := encodes_natI 1.
move=> /Forall_consP [/iipc2_St_soundness {}H].
have ?: n5 + n4 = n3 by apply: H; eassumption.
move=> /Forall_consP [/iipc2_St_soundness {}H].
have ?: n4 + 1 = n2 by apply: H; eassumption.
move=> /Forall_consP [/iipc2_St_soundness {}H].
have ?: n3 + 1 = n1 by apply: H; eassumption.
move=> _ {H} /copy [/Forall2_length_eq].
move: Qs HQs IH.
move=> [|Q9]; first done.
move=> Qs /Forall_inv HQ9 IH _ /Forall2_consE [+ _].
move: HQ9 => /typing_normal_form_poly_arrE H /H{H} [Q] [H1Q] [?].
set tS := (tS in St tS).
move=> /(typing_weakening (Gamma' := Gamma0 ++ (map Ut (map (fun x => poly_var (x + zt)) xs)) ++ (map St (tS :: tSs)) ++ (map Pt tPs))).
apply: unnest.
{
move: (Gamma0) => ? ?.
rewrite /= ?app_comm_cons ?in_app_iff /=.
clear.
by tauto.
}
move=> [?] /IH.
apply.
+
rewrite term_size_ren_term /=.
set P := (P in many_app P _).
have := term_size_many_app_le P Qs.
rewrite /P /=.
by lia.
+
by apply: normal_form_ren_term.
+
constructor; last done.
exists n5, n2, n1.
do 3 (constructor; first done).
by lia.
+
done.
-
rewrite /t_p.
rewrite [Gamma0]lock.
move=> /safe_poly_type_eqE [+ [<- _]].
move: ts HP IH.
do 5 (move=> [|?]; first done).
case; last done.
set σ := fold_right scons poly_var _.
move=> /normal_form_many_app [_ HQs] IH _.
rewrite [Ut']lock [St']lock [Pt']lock /= -[locked Ut']lock -[locked St']lock -[locked Pt']lock ?subst_poly_type_Ut' ?subst_poly_type_St' ?subst_poly_type_Pt' /= -lock.
move=> /copy [/Forall2_typing_Forall_iipc2 /Forall_consP [_]].
move=> /Forall_consP [/iipc2_Ut_unique [n5 ?]].
move=> /Forall_consP [/iipc2_Ut_unique [n4 ?]].
move=> /Forall_consP [/iipc2_Ut_unique [n3 ?]].
move=> /Forall_consP [/iipc2_Ut_unique [n2 ?]].
move=> /Forall_consP [/iipc2_Ut_unique [n1 ?]].
have ? := encodes_natI 1.
move=> /Forall_consP [/iipc2_Pt_soundness {}H].
have ?: n5 * n4 = n3 by apply: H; eassumption.
move=> /Forall_consP [/iipc2_St_soundness {}H].
have ?: n4 + 1 = n2 by apply: H; eassumption.
move=> /Forall_consP [/iipc2_St_soundness {}H].
have ?: n3 + n5 = n1 by apply: H; eassumption.
move=> _ {H} /copy [/Forall2_length_eq].
move: Qs HQs IH.
move=> [|Q9]; first done.
move=> Qs /Forall_inv HQ9 IH _ /Forall2_consE [+ _].
move: HQ9 => /typing_normal_form_poly_arrE H /H{H} [Q] [H1Q] [?].
set tP := (tP in Pt tP).
move=> /(typing_weakening (Gamma' := Gamma0 ++ (map Ut (map (fun x => poly_var (x + zt)) xs)) ++ (map St tSs) ++ (map Pt (tP :: tPs)))).
apply: unnest.
{
move: (Gamma0) => ? ?.
rewrite /= ?in_app_iff /=.
clear.
by tauto.
}
move=> [?] /IH.
apply.
+
rewrite term_size_ren_term /=.
set P := (P in many_app P _).
have := term_size_many_app_le P Qs.
rewrite /P /=.
by lia.
+
by apply: normal_form_ren_term.
+
done.
+
constructor; last done.
exists n5, n2, n1.
do 3 (constructor; first done).
by lia.
-
move=> /safe_poly_type_eqE [Hts] [<-] _ /Forall2_typing_Forall_iipc2.
rewrite map_app ?[map (subst_poly_type _) (map _ _)]map_map.
under [map _ (seq _ _)]map_ext => x do rewrite Hts -rev_length subst_poly_type_Ut'.
under [map _ h10cs]map_ext => c do (rewrite subst_poly_type_h10c_poly_type; first done).
set σ := (fold_right _ _ (rev ts)).
move=> /Forall_appP [Hδ Hh10cs].
have /list_choice [φ Hφ] : Forall (fun i => exists n, encodes_nat (σ i) n) (seq 0 δ).
{
move: Hδ => /Forall_mapP.
apply: Forall_impl => ?.
by apply: iipc2_Ut_unique.
}
exists φ => c.
move: Hh10cs δP Hφ => /Forall_mapP /Forall_forall H1 /Forall_forall H2 /Forall_forall Hφ.
move=> /copy [/H1{H1} + /H2{H2}].
case: c.
+
move=> x /iipc2_St_soundness + ? /=.
move=> /(_ (φ x) 0 1).
have -> : φ x + 0 = φ x by lia.
apply; [done | | by apply: encodes_natI | by apply: encodes_natI].
apply /Hφ /in_seq.
by lia.
+
move=> x y z /iipc2_St_soundness + ? /=.
apply; first done.
all: apply /Hφ /in_seq; by lia.
+
move=> x y z /iipc2_Pt_soundness + ? /=.
apply; first done.
all: apply /Hφ /in_seq; by lia.
}
case /in_app_iff; first by move=> /in_map_iff [?] [/last_poly_var_safe_poly_type].
case /in_app_iff; first by move=> /in_map_iff [[[? ?] ?]] [/last_poly_var_safe_poly_type].
Admitted.

Lemma inverse_transport : SysF_INH (GammaH, poly_var tt) -> H10C_SAT h10cs.
Proof.
move=> [M] /typing_of_type_assignment [P] [_] {M}.
move=> /typing_normal_form [{}P] [/construct_h10cs_solution] H /H{H}.
apply.
-
constructor.
{
exists 0, 0, 0.
do 3 (constructor; first by apply: encodes_natI).
done.
}
constructor.
{
exists 1, 0, 1.
do 3 (constructor; first by apply: encodes_natI).
done.
}
constructor.
{
exists 0, 1, 1.
do 3 (constructor; first by apply: encodes_natI).
done.
}
done.
-
constructor.
{
exists 0, 0, 0.
do 3 (constructor; first by apply: encodes_natI).
done.
}
constructor.
{
exists 1, 0, 0.
do 3 (constructor; first by apply: encodes_natI).
done.
}
Admitted.

Fact GammaUSn {n} : GammaU (S n) = GammaU n ++ [Ut (poly_num (1+n))].
Proof.
Admitted.

Fact GammaS0Sn {n} : GammaS0 (S n) = GammaS0 n ++ [St (poly_num (1+n), poly_num 0, poly_num (1+n))].
Proof.
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
by reflexivity.
